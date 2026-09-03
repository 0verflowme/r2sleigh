//! Disassembly and P-code lifting using libsla.
//!
//! This module provides runtime disassembly of instruction bytes to P-code
//! and translation to r2il using Ghidra's libsla library.

use libsla::{
    Address, AddressSpace, AddressSpaceId, BoolOp, FloatOp, GhidraSleigh, InstructionLoader, IntOp,
    IntSign, OpCode, PcodeDisassembly, PcodeInstruction, PseudoOp, Sleigh, VarnodeData,
};
use r2il::{
    MemoryClass, MemoryPermissions, PointerHint, R2ILBlock, R2ILOp, ScalarKind, SpaceId,
    StorageClass, Varnode, select_register_name,
};
use r2source::SourceEndianness;
use r2source::{
    AdvisorySuccessorKind, CanonicalStorageId, CanonicalStorageSpace, MachineProfile,
    OwnedFunctionSnapshot, SourceFunctionInterface,
};
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::sync::Arc;

use crate::translate::{self, PcodeSource};
use crate::{LiftError, Result};

/// A disassembler that uses libsla to lift instructions to r2il.
pub struct Disassembler {
    /// The underlying Ghidra Sleigh instance
    sleigh: GhidraSleigh,
    /// Architecture name
    arch_name: String,
    /// Canonical register names by (offset, size)
    reg_name_map: HashMap<(u64, u32), String>,
    /// Exact mapping extracted with the architecture metadata for this session.
    space_map: HashMap<AddressSpaceId, SpaceId>,
    /// Register the processor spec names as the program counter.
    program_counter: String,
    /// Opaque authority present only for an embedded trusted Sleigh profile.
    genuine_authority: Option<GenuineLiftAuthority>,
    trusted_profile: Option<TrustedSleighProfile>,
}

/// Embedded Sleigh profiles allowed to mint certifying lift authority.
///
/// Arbitrary caller-supplied SLA/pspec bytes remain useful for analysis, but
/// cannot enter the certification pipeline. Keeping the trust root here makes
/// the exact specification bundle—not a caller-provided name—the authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustedSleighProfile {
    #[cfg(feature = "x86")]
    X86,
    #[cfg(feature = "x86")]
    X86_64,
    #[cfg(feature = "arm")]
    ArmCortexLe,
    #[cfg(feature = "arm")]
    Aarch64Le,
    #[cfg(feature = "arm")]
    Aarch64AppleSilicon,
    #[cfg(feature = "mips")]
    Mips32Be,
    #[cfg(feature = "mips")]
    Mips32Le,
    #[cfg(feature = "mips")]
    Mips64Be,
    #[cfg(feature = "mips")]
    Mips64Le,
    #[cfg(feature = "riscv")]
    RiscV32Gc,
    #[cfg(feature = "riscv")]
    RiscV64Gc,
}

impl TrustedSleighProfile {
    fn specification(self) -> (&'static [u8], &'static str, &'static str) {
        match self {
            #[cfg(feature = "x86")]
            Self::X86 => (
                sleigh_config::processor_x86::SLA_X86,
                sleigh_config::processor_x86::PSPEC_X86,
                "x86",
            ),
            #[cfg(feature = "x86")]
            Self::X86_64 => (
                sleigh_config::processor_x86::SLA_X86_64,
                sleigh_config::processor_x86::PSPEC_X86_64,
                "x86-64",
            ),
            #[cfg(feature = "arm")]
            // Ghidra's own ARM.ldefs pairs ARM8_le with ARMt, which leaves
            // TMode clear. A Cortex pspec sets TMode, and Cortex-M is
            // Thumb-only, so pairing it here would lift every A32 instruction
            // as Thumb: wrong instruction, wrong length, wrong control flow.
            Self::ArmCortexLe => (
                sleigh_config::processor_arm::SLA_ARM8_LE,
                sleigh_config::processor_arm::PSPEC_ARMT,
                "ARM",
            ),
            #[cfg(feature = "arm")]
            Self::Aarch64Le => (
                sleigh_config::processor_aarch64::SLA_AARCH64,
                sleigh_config::processor_aarch64::PSPEC_AARCH64,
                "aarch64",
            ),
            #[cfg(feature = "arm")]
            Self::Aarch64AppleSilicon => (
                sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
                sleigh_config::processor_aarch64::PSPEC_AARCH64,
                "aarch64",
            ),
            #[cfg(feature = "mips")]
            Self::Mips32Be => (
                sleigh_config::processor_mips::SLA_MIPS32BE,
                sleigh_config::processor_mips::PSPEC_MIPS32,
                "mips32be",
            ),
            #[cfg(feature = "mips")]
            Self::Mips32Le => (
                sleigh_config::processor_mips::SLA_MIPS32LE,
                sleigh_config::processor_mips::PSPEC_MIPS32,
                "mips32le",
            ),
            #[cfg(feature = "mips")]
            Self::Mips64Be => (
                sleigh_config::processor_mips::SLA_MIPS64BE,
                sleigh_config::processor_mips::PSPEC_MIPS64,
                "mips64be",
            ),
            #[cfg(feature = "mips")]
            Self::Mips64Le => (
                sleigh_config::processor_mips::SLA_MIPS64LE,
                sleigh_config::processor_mips::PSPEC_MIPS64,
                "mips64le",
            ),
            #[cfg(feature = "riscv")]
            Self::RiscV32Gc => (
                sleigh_config::processor_riscv::SLA_RISCV_ILP32D,
                sleigh_config::processor_riscv::PSPEC_RV32GC,
                "riscv32",
            ),
            #[cfg(feature = "riscv")]
            Self::RiscV64Gc => (
                sleigh_config::processor_riscv::SLA_RISCV_LP64D,
                sleigh_config::processor_riscv::PSPEC_RV64GC,
                "riscv64",
            ),
        }
    }

    /// Select an embedded specification from one exact source-owned machine
    /// tuple. Only tuples manually verified against the active radare analyzer
    /// are admitted; aliases, empty CPU defaults, and inferred host values are
    /// deliberately unsupported.
    fn from_machine(machine: &MachineProfile) -> Result<Self> {
        Self::from_tuple(
            machine.arch_id(),
            machine.cpu_id(),
            machine.bits(),
            machine.endianness(),
        )
    }

    fn from_tuple(
        arch_id: &str,
        cpu_id: &str,
        bits: u32,
        endianness: SourceEndianness,
    ) -> Result<Self> {
        match (arch_id, cpu_id, bits, endianness) {
            #[cfg(feature = "x86")]
            ("x86", "x86", 32, SourceEndianness::Little) => Ok(Self::X86),
            #[cfg(feature = "x86")]
            ("x86", "x86", 64, SourceEndianness::Little) => Ok(Self::X86_64),
            #[cfg(feature = "arm")]
            ("arm", "arm", 64, SourceEndianness::Little) => Ok(Self::Aarch64Le),
            _ => Err(LiftError::Unsupported(format!(
                "no manually verified trusted Sleigh profile for source tuple {}/{}/{}/{:?}",
                arch_id, cpu_id, bits, endianness
            ))),
        }
    }
}

fn is_exact_top_level_address_register(
    arch: &r2il::ArchSpec,
    storage: CanonicalStorageId,
    address_size: u32,
) -> bool {
    storage.space == CanonicalStorageSpace::Register
        && storage.size == address_size
        && arch.registers.iter().any(|register| {
            register.parent.is_none()
                && register.offset == storage.offset
                && register.size == storage.size
        })
        && !arch.registers.iter().any(|register| {
            register.size > storage.size
                && register.offset <= storage.offset
                && register
                    .offset
                    .checked_add(u64::from(register.size))
                    .zip(storage.offset.checked_add(u64::from(storage.size)))
                    .is_some_and(|(register_end, storage_end)| register_end >= storage_end)
        })
}

fn register_storages_are_disjoint(first: CanonicalStorageId, second: CanonicalStorageId) -> bool {
    if first.space != second.space {
        return true;
    }
    first
        .offset
        .checked_add(u64::from(first.size))
        .zip(second.offset.checked_add(u64::from(second.size)))
        .is_some_and(|(first_end, second_end)| {
            first_end <= second.offset || second_end <= first.offset
        })
}

/// Where the lifted architecture puts the register the source named.
///
/// Spelling differs between the two: radare2 writes x86 register names in lower
/// case where the Sleigh specification writes them in upper case, and that is a
/// difference in spelling, not in register. Case is therefore folded, and
/// nothing else is: a name the architecture does not define resolves to
/// nothing, because placing an unrecognised carrier by guesswork is how a
/// carrier ends up at another register's offset.
fn arch_register_storage(arch: &r2il::ArchSpec, name: &str) -> Option<CanonicalStorageId> {
    let register = arch
        .get_register(name)
        .or_else(|| arch.get_register(&name.to_ascii_uppercase()))
        .or_else(|| arch.get_register(&name.to_ascii_lowercase()))?;
    Some(CanonicalStorageId {
        space: r2source::CanonicalStorageSpace::Register,
        offset: register.offset,
        size: register.size,
    })
}

/// Restate a capture's role carriers in the lifted architecture's numbering.
///
/// The capture states each carrier as a name plus an offset into its own
/// register arena. Only the name crosses over, so each carrier is looked up
/// again here and a carrier the architecture cannot place is dropped. Dropping
/// costs the certificates that need that carrier; keeping the capture's offset
/// would instead assert that some unrelated register is the return address,
/// which every consumer downstream would then believe.
fn arch_resolved_source(
    source: OwnedFunctionSnapshot,
    arch: &r2il::ArchSpec,
) -> Result<OwnedFunctionSnapshot> {
    let resolve = |name: Option<&str>| name.and_then(|name| arch_register_storage(arch, name));
    let interface = match source.function_interface() {
        Some(interface) => {
            let names = interface.role_register_names();
            Some(
                interface
                    .clone()
                    .with_arch_resolved_role_carriers(
                        resolve(names.return_address()),
                        resolve(names.stack_pointer()),
                        resolve(names.frame_pointer()),
                    )
                    .map_err(|error| {
                        LiftError::Unsupported(format!(
                            "captured interface carriers do not resolve against the lifted \
                             architecture: {error:?}"
                        ))
                    })?,
            )
        }
        None => None,
    };
    let role_names = source.machine_roles().role_register_names();
    let roles = source
        .machine_roles()
        .with_arch_resolved_carriers(
            resolve(role_names.return_address()),
            resolve(role_names.stack_pointer()),
        )
        .map_err(|error| {
            LiftError::Unsupported(format!(
                "captured machine carriers do not resolve against the lifted architecture: \
                 {error:?}"
            ))
        })?;
    Ok(source.with_arch_resolved_role_carriers(interface, roles))
}

fn captured_frame_pointer_storage_matches_arch(
    interface: &SourceFunctionInterface,
    arch: &r2il::ArchSpec,
) -> bool {
    let Some(frame_pointer) = interface.frame_pointer_storage() else {
        return true;
    };
    let Some(return_address) = interface.return_address_storage() else {
        return false;
    };
    let Some(stack_pointer) = interface.stack_pointer_storage() else {
        return false;
    };
    let address_size = r2il::effective_arch_address_size(arch);
    interface.frame_pointer_storage_is_valid(frame_pointer)
        && interface.return_address_storage_is_valid(return_address)
        && interface.stack_pointer_storage_is_valid(stack_pointer)
        && is_exact_top_level_address_register(arch, frame_pointer, address_size)
        && is_exact_top_level_address_register(arch, return_address, address_size)
        && is_exact_top_level_address_register(arch, stack_pointer, address_size)
        && register_storages_are_disjoint(frame_pointer, return_address)
        && register_storages_are_disjoint(frame_pointer, stack_pointer)
        && register_storages_are_disjoint(return_address, stack_pointer)
}

fn captured_return_mechanism_matches_arch(
    interface: &SourceFunctionInterface,
    arch: &r2il::ArchSpec,
) -> bool {
    let Some(mechanism) = interface.return_mechanism() else {
        return true;
    };
    let address_size = mechanism.address_size_bytes();
    let Some(address_bits) = address_size.checked_mul(8) else {
        return false;
    };
    if address_size <= 1
        || arch.addr_size != address_size
        || mechanism.stack_offset() != 0
        || mechanism.slot_size_bytes() != address_size
        || mechanism.stack_pointer_delta_bytes() != address_size
    {
        return false;
    }
    let mut ram_spaces = arch.spaces.iter().filter(|space| space.id == SpaceId::Ram);
    let Some(ram) = ram_spaces.next() else {
        return false;
    };
    if ram_spaces.next().is_some()
        || ram.word_size != 1
        || ram.addr_size.checked_mul(8) != Some(address_bits)
    {
        return false;
    }
    let Some(return_address) = interface.return_address_storage() else {
        return false;
    };
    let Some(stack_pointer) = interface.stack_pointer_storage() else {
        return false;
    };
    is_exact_top_level_address_register(arch, return_address, address_size)
        && is_exact_top_level_address_register(arch, stack_pointer, address_size)
}

/// Schema of the exact lift-origin manifest retained by genuine blocks.
pub const GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION: u32 = 2;

#[derive(Debug)]
struct GenuineLiftAuthorityState {
    arch_name: Arc<str>,
    arch: Arc<r2il::ArchSpec>,
    manifest_hash: u64,
}

/// Opaque run-local authority for one exact Sleigh configuration.
///
/// Equality is session identity, not manifest equality. Independently loading
/// identical specifications therefore cannot replay proof authority, while the
/// stable manifest hash remains available for diagnostics and cache partitioning.
#[derive(Clone)]
pub struct GenuineLiftAuthority(Arc<GenuineLiftAuthorityState>);

impl GenuineLiftAuthority {
    fn new(
        sla_bytes: Arc<[u8]>,
        pspec: Arc<str>,
        arch_name: Arc<str>,
        arch: Arc<r2il::ArchSpec>,
    ) -> Self {
        let manifest_hash = stable_lift_manifest_hash(&sla_bytes, &pspec, &arch_name);
        Self(Arc::new(GenuineLiftAuthorityState {
            arch_name,
            arch,
            manifest_hash,
        }))
    }

    /// Exact architecture derived from the retained Sleigh specification.
    pub fn arch_spec(&self) -> &r2il::ArchSpec {
        &self.0.arch
    }

    pub fn arch_name(&self) -> &str {
        &self.0.arch_name
    }

    pub const fn schema_version(&self) -> u32 {
        GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION
    }

    /// Stable diagnostic identity. This is never proof authority.
    pub fn manifest_hash(&self) -> u64 {
        self.0.manifest_hash
    }

    pub fn same_session(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl std::fmt::Debug for GenuineLiftAuthority {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GenuineLiftAuthority")
            .field("schema_version", &self.schema_version())
            .field("arch_name", &self.arch_name())
            .field("manifest_hash", &self.manifest_hash())
            .finish_non_exhaustive()
    }
}

impl PartialEq for GenuineLiftAuthority {
    fn eq(&self, other: &Self) -> bool {
        self.same_session(other)
    }
}

impl Eq for GenuineLiftAuthority {}

impl Hash for GenuineLiftAuthority {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}

/// One immutable block produced directly by a genuine Disassembler session.
#[derive(Debug, Clone)]
pub struct GenuineLiftedBlock {
    authority: GenuineLiftAuthority,
    block: R2ILBlock,
    source_bytes: Arc<[u8]>,
    instruction_spans: Arc<[GenuineInstructionSpan]>,
}

/// Exact native instruction coverage retained even for zero-op instructions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GenuineInstructionSpan {
    addr: u64,
    size: u32,
    first_canonical_op: u64,
    canonical_op_count: u64,
}

impl GenuineInstructionSpan {
    pub const fn addr(self) -> u64 {
        self.addr
    }

    pub const fn size(self) -> u32 {
        self.size
    }

    /// First operation in the exact canonical P-code stream for this native
    /// instruction. Zero-op spans point at the next canonical operation.
    pub const fn first_canonical_op(self) -> u64 {
        self.first_canonical_op
    }

    /// Number of exact canonical P-code operations emitted for this native
    /// instruction. Zero means the trusted translator supplied no semantics;
    /// it does not by itself prove that the instruction is effect-free.
    pub const fn canonical_op_count(self) -> u64 {
        self.canonical_op_count
    }
}

impl GenuineLiftedBlock {
    pub fn block(&self) -> &R2ILBlock {
        &self.block
    }

    pub fn source_bytes(&self) -> &[u8] {
        &self.source_bytes
    }

    pub fn instruction_spans(&self) -> &[GenuineInstructionSpan] {
        &self.instruction_spans
    }

    pub fn authority(&self) -> &GenuineLiftAuthority {
        &self.authority
    }
}

/// One exact source-owned basic-block extent.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GenuineFunctionBlockRange {
    addr: u64,
    size: u32,
}

impl GenuineFunctionBlockRange {
    pub(crate) const fn new(addr: u64, size: u32) -> Self {
        Self { addr, size }
    }

    pub const fn addr(self) -> u64 {
        self.addr
    }

    pub const fn size(self) -> u32 {
        self.size
    }
}

/// Immutable source declaration of the complete function block layout.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenuineFunctionLayout {
    revision_identity: Arc<[u8]>,
    entry_addr: u64,
    blocks: Arc<[GenuineFunctionBlockRange]>,
    external_exits: Arc<[u64]>,
}

impl GenuineFunctionLayout {
    pub(crate) fn new(
        revision_identity: impl Into<Vec<u8>>,
        entry_addr: u64,
        blocks: impl IntoIterator<Item = GenuineFunctionBlockRange>,
        external_exits: impl IntoIterator<Item = u64>,
    ) -> Result<Self> {
        let revision_identity = revision_identity.into();
        let blocks = blocks.into_iter().collect::<Vec<_>>();
        if revision_identity.is_empty() || blocks.is_empty() {
            return Err(LiftError::Parse(
                "genuine function layout requires revision identity and blocks".to_string(),
            ));
        }
        let mut previous_end = None;
        let mut entry_found = false;
        for block in &blocks {
            if block.size == 0 {
                return Err(LiftError::Parse(
                    "genuine function layout contains an empty block".to_string(),
                ));
            }
            let end = block
                .addr
                .checked_add(u64::from(block.size))
                .ok_or_else(|| {
                    LiftError::Parse("genuine function block range overflows".to_string())
                })?;
            if previous_end.is_some_and(|previous| block.addr < previous) {
                return Err(LiftError::Parse(
                    "genuine function layout must be ordered and non-overlapping".to_string(),
                ));
            }
            entry_found |= block.addr == entry_addr;
            previous_end = Some(end);
        }
        if !entry_found {
            return Err(LiftError::Parse(
                "genuine function entry is not a declared block".to_string(),
            ));
        }
        let mut external_exits = external_exits.into_iter().collect::<Vec<_>>();
        external_exits.sort_unstable();
        if external_exits.windows(2).any(|pair| pair[0] == pair[1])
            || external_exits.iter().any(|target| {
                blocks.iter().any(|block| {
                    block
                        .addr
                        .checked_add(u64::from(block.size))
                        .is_some_and(|end| block.addr <= *target && *target < end)
                })
            })
        {
            return Err(LiftError::Parse(
                "genuine function external exits must be unique and outside the layout".to_string(),
            ));
        }
        Ok(Self {
            revision_identity: revision_identity.into(),
            entry_addr,
            blocks: blocks.into(),
            external_exits: external_exits.into(),
        })
    }

    pub fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn entry_addr(&self) -> u64 {
        self.entry_addr
    }

    pub fn blocks(&self) -> &[GenuineFunctionBlockRange] {
        &self.blocks
    }

    pub fn external_exits(&self) -> &[u64] {
        &self.external_exits
    }
}

/// Opaque identity of one complete exact-layout genuine lift.
#[derive(Debug)]
struct GenuineLiftedFunctionAuthorityState {
    lift: GenuineLiftAuthority,
    layout: GenuineFunctionLayout,
    source_manifest_hash: u64,
}

/// Opaque run-local identity of one complete exact-layout genuine lift.
#[derive(Clone)]
pub struct GenuineLiftedFunctionAuthority(Arc<GenuineLiftedFunctionAuthorityState>);

impl GenuineLiftedFunctionAuthority {
    pub fn lift_authority(&self) -> &GenuineLiftAuthority {
        &self.0.lift
    }

    pub fn layout(&self) -> &GenuineFunctionLayout {
        &self.0.layout
    }

    /// Stable diagnostic identity of configuration, layout, and source bytes.
    pub fn source_manifest_hash(&self) -> u64 {
        self.0.source_manifest_hash
    }

    /// Whether both values name the same exact function-lift event.
    pub fn same_lift(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl std::fmt::Debug for GenuineLiftedFunctionAuthority {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GenuineLiftedFunctionAuthority")
            .field("lift", self.lift_authority())
            .field("layout", self.layout())
            .field("source_manifest_hash", &self.source_manifest_hash())
            .finish_non_exhaustive()
    }
}

impl PartialEq for GenuineLiftedFunctionAuthority {
    fn eq(&self, other: &Self) -> bool {
        self.same_lift(other)
    }
}

impl Eq for GenuineLiftedFunctionAuthority {}

impl Hash for GenuineLiftedFunctionAuthority {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}

/// Exact-layout immutable blocks from one exact lift session and policy.
#[derive(Debug, Clone)]
pub struct GenuineLiftedFunction {
    authority: GenuineLiftedFunctionAuthority,
    blocks: Arc<[GenuineLiftedBlock]>,
}

/// Canonical lift retaining the exact opaque source capture that supplied its
/// bytes and typed function interface. Detached genuine blocks/layouts remain
/// analysis-only and cannot construct this type.
#[derive(Debug, Clone)]
pub struct TrustedLiftedFunction {
    source: OwnedFunctionSnapshot,
    lifted: GenuineLiftedFunction,
}

impl TrustedLiftedFunction {
    pub fn source(&self) -> &OwnedFunctionSnapshot {
        &self.source
    }

    pub fn lifted(&self) -> &GenuineLiftedFunction {
        &self.lifted
    }
}

impl GenuineLiftedFunction {
    pub(crate) fn try_from_layout(
        layout: GenuineFunctionLayout,
        blocks: Vec<GenuineLiftedBlock>,
    ) -> Result<Self> {
        let Some(first) = blocks.first() else {
            return Err(LiftError::Parse(
                "genuine lifted function requires at least one block".to_string(),
            ));
        };
        if blocks.len() != layout.blocks.len() {
            return Err(LiftError::Parse(
                "genuine lift does not cover the exact declared block layout".to_string(),
            ));
        }
        let lift = first.authority.clone();
        for (declared, block) in layout.blocks.iter().zip(&blocks) {
            if !lift.same_session(&block.authority) {
                return Err(LiftError::Parse(
                    "genuine lifted function cannot mix disassembler sessions".to_string(),
                ));
            }
            if block.block.addr != declared.addr
                || block.block.size != declared.size
                || usize::try_from(declared.size) != Ok(block.source_bytes.len())
                || !genuine_instruction_spans_cover_block(block)
            {
                return Err(LiftError::Parse(
                    "genuine lifted block does not match its declared extent".to_string(),
                ));
            }
        }
        let successor_manifest = validate_genuine_function_cfg(&layout, &blocks)?;
        let source_manifest_hash =
            stable_genuine_function_manifest_hash(&lift, &layout, &blocks, &successor_manifest);
        Ok(Self {
            authority: GenuineLiftedFunctionAuthority(Arc::new(
                GenuineLiftedFunctionAuthorityState {
                    lift,
                    layout,
                    source_manifest_hash,
                },
            )),
            blocks: blocks.into(),
        })
    }

    pub fn authority(&self) -> &GenuineLiftedFunctionAuthority {
        &self.authority
    }

    pub fn arch_spec(&self) -> &r2il::ArchSpec {
        self.authority.lift_authority().arch_spec()
    }

    pub fn blocks(&self) -> &[GenuineLiftedBlock] {
        &self.blocks
    }
}

fn genuine_instruction_spans_cover_block(block: &GenuineLiftedBlock) -> bool {
    let mut expected = block.block.addr;
    let mut expected_op = 0usize;
    if block.instruction_spans.is_empty() {
        return false;
    }
    for span in block.instruction_spans.iter() {
        if span.addr != expected
            || span.size == 0
            || usize::try_from(span.first_canonical_op) != Ok(expected_op)
        {
            return false;
        }
        let Some(next) = expected.checked_add(u64::from(span.size)) else {
            return false;
        };
        let Ok(op_count) = usize::try_from(span.canonical_op_count) else {
            return false;
        };
        let Some(next_op) = expected_op.checked_add(op_count) else {
            return false;
        };
        if next_op > block.block.ops.len()
            || (expected_op..next_op).any(|op_index| {
                block
                    .block
                    .op_metadata(op_index)
                    .and_then(|metadata| metadata.instruction_addr)
                    != Some(span.addr)
            })
        {
            return false;
        }
        expected = next;
        expected_op = next_op;
    }
    block.block.addr.checked_add(u64::from(block.block.size)) == Some(expected)
        && expected_op == block.block.ops.len()
}

fn constant_control_target(target: &Varnode) -> Option<u64> {
    (matches!(target.space, SpaceId::Const | SpaceId::Ram) && target.size > 0)
        .then_some(target.offset)
}

/// True when this operation is p-code control flow internal to one machine
/// instruction rather than the block's terminator.
///
/// Sleigh emits these routinely: a conditional move becomes a conditional
/// branch over the move, and a conditional compare branches over the rest of
/// its own operations. Both target the following instruction, which is exactly
/// what an ordinary branch to the next block targets, so the target alone
/// cannot tell them apart. What distinguishes them is that further operations
/// of the same instruction still follow: a terminator is the last thing its
/// instruction does.
fn control_op_is_intra_instruction(block: &GenuineLiftedBlock, op_index: usize) -> bool {
    let Some(instruction) = block
        .block
        .op_metadata(op_index)
        .and_then(|metadata| metadata.instruction_addr)
    else {
        return false;
    };
    (op_index + 1..block.block.ops.len()).any(|later| {
        block
            .block
            .op_metadata(later)
            .and_then(|metadata| metadata.instruction_addr)
            == Some(instruction)
    })
}

/// The operation that decides where this block goes, if any.
fn block_terminator(block: &GenuineLiftedBlock) -> Option<&R2ILOp> {
    block
        .block
        .ops
        .iter()
        .enumerate()
        .rev()
        .find(|(index, op)| op.is_control_flow() && !control_op_is_intra_instruction(block, *index))
        .map(|(_, op)| op)
}

fn genuine_block_successors(block: &GenuineLiftedBlock) -> Result<Vec<u64>> {
    let fallthrough = block
        .block
        .addr
        .checked_add(u64::from(block.block.size))
        .ok_or_else(|| LiftError::Parse("genuine block fallthrough overflows".to_string()))?;
    let last_instruction = block
        .instruction_spans
        .last()
        .ok_or_else(|| LiftError::Parse("genuine block has no native instruction".to_string()))?
        .addr;
    for (op_index, op) in block.block.ops.iter().enumerate() {
        // Only an operation that decides where this block goes has to be its
        // last instruction. An indirect branch the lift could not resolve
        // decides nothing, and traps are modelled that way: Ghidra lifts a
        // guard instruction such as `brk` into a user operation writing pc
        // followed by a branch through it, which routinely sits mid-block.
        //
        // Exempting it cannot let a wrong successor set through. If such a
        // branch were really this block's terminator, the block would name no
        // successors while the advisory graph names its edges, and comparing
        // the two refuses the function.
        // P-code has control flow inside a single instruction. Sleigh lifts
        // AArch64 `ccmp`, for example, into a conditional branch that skips the
        // rest of that instruction's own operations by targeting the next
        // instruction. Such a branch never leaves the block, so it decides no
        // successor and may sit anywhere in it.
        let decides_successors = match op {
            R2ILOp::Branch { .. } | R2ILOp::CBranch { .. } => {
                !control_op_is_intra_instruction(block, op_index)
            }
            R2ILOp::Return { .. } | R2ILOp::Breakpoint => true,
            R2ILOp::BranchInd { .. } => block.block.switch_info.is_some(),
            _ => false,
        };
        if decides_successors
            && block
                .block
                .op_metadata(op_index)
                .and_then(|metadata| metadata.instruction_addr)
                != Some(last_instruction)
        {
            return Err(LiftError::Parse(
                "genuine basic block contains instructions after a control terminator".to_string(),
            ));
        }
    }
    match block_terminator(block) {
        Some(R2ILOp::Return { .. } | R2ILOp::Breakpoint) => Ok(Vec::new()),
        Some(R2ILOp::Branch { target }) => constant_control_target(target)
            .map(|target| vec![target])
            .ok_or_else(|| {
                LiftError::Parse("genuine direct branch target is not constant".to_string())
            }),
        Some(R2ILOp::CBranch { target, .. }) => constant_control_target(target)
            .map(|target| vec![target, fallthrough])
            .ok_or_else(|| {
                LiftError::Parse("genuine conditional branch target is not constant".to_string())
            }),
        // An indirect branch whose target the lift did not resolve leaves this
        // function through an address the machine does not know, so it
        // contributes no edge back into the function's own blocks. It is not
        // treated as a proof that control stops here: the operation that
        // produced the target is still in the block and still carries its own
        // obligation.
        //
        // A resolved jump table is a different case. Its targets are the
        // function's own blocks, so the advisory graph names edges the machine
        // does not, and the comparison against that graph refuses the function
        // rather than silently dropping them.
        Some(R2ILOp::BranchInd { .. }) => match block.block.switch_info.as_ref() {
            Some(switch) => {
                let mut successors = switch
                    .cases
                    .iter()
                    .map(|case| case.target)
                    .collect::<Vec<_>>();
                successors.extend(switch.default_target);
                successors.sort_unstable();
                successors.dedup();
                Ok(successors)
            }
            None => Ok(Vec::new()),
        },
        Some(R2ILOp::Call { .. } | R2ILOp::CallInd { .. }) | None => Ok(vec![fallthrough]),
        Some(_) => unreachable!("control-flow filter returned a non-control operation"),
    }
}

fn validate_genuine_function_cfg(
    layout: &GenuineFunctionLayout,
    blocks: &[GenuineLiftedBlock],
) -> Result<Vec<Vec<u64>>> {
    let starts = layout
        .blocks
        .iter()
        .map(|block| block.addr)
        .collect::<HashSet<_>>();
    // A successor that is not one of this function's block starts leaves the
    // function. What must never happen is a target landing part-way into a
    // block, because that would mean the lift decoded an instruction boundary
    // the block layout does not have. Requiring instead that every exit appear
    // in the source's declared exit list would refuse ordinary tail calls: the
    // source builds that list from the function it analysed, which records no
    // successor for a branch leaving the function at all.
    let lands_offcut = |target: u64| {
        !starts.contains(&target)
            && layout.blocks.iter().any(|block| {
                target > block.addr()
                    && target < block.addr().saturating_add(u64::from(block.size()))
            })
    };
    let mut internal_successors = HashMap::<u64, Vec<u64>>::new();
    let mut successor_manifest = Vec::with_capacity(blocks.len());
    for block in blocks {
        let successors = genuine_block_successors(block)?;
        if successors.iter().copied().any(lands_offcut) {
            return Err(LiftError::Parse(
                "genuine function branches into the middle of one of its blocks".to_string(),
            ));
        }
        // An indirect branch the lift could not resolve may land on any of this
        // function's blocks. Recording no edge would let the reachability check
        // below conclude that the blocks only it reaches were invented, which
        // is the machine's ignorance stated as a finding about the program.
        let internal = if matches!(block_terminator(block), Some(R2ILOp::BranchInd { .. }))
            && block.block.switch_info.is_none()
        {
            starts.iter().copied().collect()
        } else {
            successors
                .iter()
                .copied()
                .filter(|successor| starts.contains(successor))
                .collect()
        };
        internal_successors.insert(block.block.addr, internal);
        successor_manifest.push(successors);
    }
    let mut reached = HashSet::new();
    let mut queue = VecDeque::from([layout.entry_addr]);
    while let Some(block) = queue.pop_front() {
        if !reached.insert(block) {
            continue;
        }
        let successors = internal_successors.get(&block).ok_or_else(|| {
            LiftError::Parse("genuine function entry is missing from lifted blocks".to_string())
        })?;
        queue.extend(successors.iter().copied());
    }
    if reached.len() != blocks.len() {
        return Err(LiftError::Parse(
            "genuine function contains blocks unreachable from its exact entry".to_string(),
        ));
    }
    Ok(successor_manifest)
}

fn typed_genuine_block_successors(
    block: &GenuineLiftedBlock,
) -> Result<Vec<(AdvisorySuccessorKind, u64, Option<u64>)>> {
    let fallthrough = block
        .block
        .addr
        .checked_add(u64::from(block.block.size))
        .ok_or_else(|| LiftError::Parse("trusted block fallthrough overflows".to_string()))?;
    match block_terminator(block) {
        Some(R2ILOp::Return { .. } | R2ILOp::Breakpoint) => Ok(Vec::new()),
        Some(R2ILOp::Branch { target }) => constant_control_target(target)
            .map(|target| vec![(AdvisorySuccessorKind::Direct, target, None)])
            .ok_or_else(|| {
                LiftError::Parse("trusted direct branch target is not constant".to_string())
            }),
        Some(R2ILOp::CBranch { target, .. }) => constant_control_target(target)
            .map(|target| {
                vec![
                    (AdvisorySuccessorKind::Direct, target, None),
                    (AdvisorySuccessorKind::Fallthrough, fallthrough, None),
                ]
            })
            .ok_or_else(|| {
                LiftError::Parse("trusted conditional branch target is not constant".to_string())
            }),
        // An unresolved indirect branch names no edge back into this function:
        // the machine does not know where it goes.
        //
        // A jump table is different only in that radare2 resolved it and put
        // the result on the block. That resolution is not machine evidence and
        // grants no authority, but it is still the flow this function has, and
        // reporting no successors here would say the switch block goes nowhere
        // -- leaving every block it reaches unreachable and the function
        // refused. The edges are reported so the graphs describe the same
        // function; what may be claimed about them is settled downstream,
        // where an unproven construct is marked rather than rejected.
        Some(R2ILOp::BranchInd { .. }) => Ok(match block.block.switch_info.as_ref() {
            Some(switch) => {
                let mut successors = switch
                    .cases
                    .iter()
                    .map(|case| {
                        (
                            AdvisorySuccessorKind::SwitchCase,
                            case.target,
                            Some(case.value),
                        )
                    })
                    .collect::<Vec<_>>();
                successors.extend(
                    switch
                        .default_target
                        .map(|target| (AdvisorySuccessorKind::SwitchDefault, target, None)),
                );
                successors
            }
            None => Vec::new(),
        }),
        // A call leaves the block by falling through to the next instruction.
        // Where it goes in between is a property of the callee, not of this
        // function's control flow, so it contributes no successor of its own.
        // This matches the machine-side closure check, which has always treated
        // a call terminator as a fallthrough.
        Some(R2ILOp::Call { .. } | R2ILOp::CallInd { .. }) => Ok(vec![(
            AdvisorySuccessorKind::Fallthrough,
            fallthrough,
            None,
        )]),
        None => Ok(vec![(
            AdvisorySuccessorKind::Fallthrough,
            fallthrough,
            None,
        )]),
        Some(_) => unreachable!("control-flow filter returned a non-control operation"),
    }
}

fn validate_owned_snapshot_cfg(
    source: &OwnedFunctionSnapshot,
    blocks: &[GenuineLiftedBlock],
) -> Result<()> {
    // Advisory call sites are diagnostic only: they never granted authority to
    // anything, and no consumer reads them. Refusing a function because radare2
    // reported the calls it found rejected more information rather than less,
    // and it suppressed every function that calls anything. Call boundaries are
    // certified from machine evidence, and residualize when that evidence is
    // absent.
    if source.image().blocks().len() != blocks.len() {
        return Err(LiftError::Parse(
            "trusted lift does not cover every owned source block".to_string(),
        ));
    }
    for (source_block, lifted_block) in source.image().blocks().iter().zip(blocks) {
        if source_block.address() != lifted_block.block().addr {
            return Err(LiftError::Parse(
                "trusted lift block order differs from owned source".to_string(),
            ));
        }
        let mut machine = typed_genuine_block_successors(lifted_block)?;
        machine.sort_unstable();
        if machine.windows(2).any(|pair| pair[0] == pair[1]) {
            return Err(LiftError::Parse(
                "trusted machine CFG contains a duplicate successor".to_string(),
            ));
        }
        let mut advisory = source_block
            .successors()
            .iter()
            .map(|successor| (successor.kind(), successor.target(), successor.case_value()))
            .collect::<Vec<_>>();
        advisory.sort_unstable();
        // The two graphs are scoped differently and cannot be compared for
        // equality. The advisory graph is the function radare2 analysed, so it
        // stops at the function's edge: a tail call records no successor at
        // all, because its target is another function. The machine graph
        // describes the instructions, so it sees that branch.
        //
        // What must hold is that the lift did not lose or invent flow *inside*
        // the function: every edge landing on one of this function's own blocks
        // must appear in both. An edge leaving them is the function exiting,
        // which the machine may know about and radare2 may not.
        let block_starts = source
            .image()
            .blocks()
            .iter()
            .map(|block| block.address())
            .collect::<BTreeSet<_>>();
        let internal = |successors: &[(AdvisorySuccessorKind, u64, Option<u64>)]| {
            successors
                .iter()
                .copied()
                .filter(|(_, target, _)| block_starts.contains(target))
                .collect::<Vec<_>>()
        };
        // The two graphs answer the same question from different evidence, and
        // each knows something the other cannot. Where they disagree, the
        // question is whether one of them is ignorant or the two contradict
        // each other; only a contradiction refuses the function.
        //
        // The machine cannot resolve a jump table, so it names no edge out of
        // an indirect branch while radare2, having analysed the table, names
        // every case. The machine also assumes a call returns, because whether
        // it does is a property of the callee; radare2 knows `exit` does not
        // and ends the block there. Neither difference is a disagreement about
        // this function's instructions, and refusing on either rejects most
        // real programs -- the first takes out every entry point that switches,
        // the second every one that can fail.
        //
        // What certifies nothing still describes the flow, and is marked
        // unproven where that matters rather than discarded here.
        let terminator = block_terminator(lifted_block);
        let machine_internal = internal(&machine);
        let advisory_internal = internal(&advisory);
        let machine_only = machine_internal
            .iter()
            .filter(|edge| !advisory_internal.contains(edge))
            .copied()
            .collect::<Vec<_>>();
        let advisory_only = advisory_internal
            .iter()
            .filter(|edge| !machine_internal.contains(edge))
            .copied()
            .collect::<Vec<_>>();

        let call_may_not_return = matches!(
            terminator,
            Some(R2ILOp::Call { .. } | R2ILOp::CallInd { .. })
        ) && machine_only
            .iter()
            .all(|(kind, _, _)| *kind == AdvisorySuccessorKind::Fallthrough);
        let table_unresolved = matches!(terminator, Some(R2ILOp::BranchInd { .. }))
            && lifted_block.block().switch_info.is_none();

        if (!machine_only.is_empty() && !call_may_not_return)
            || (!advisory_only.is_empty() && !table_unresolved)
        {
            return Err(LiftError::Parse(format!(
                "machine-derived CFG contradicts the owned advisory source CFG at {:#x}: \
                 machine names {machine_only:?}, source names {advisory_only:?}",
                lifted_block.block().addr,
            )));
        }
    }
    Ok(())
}

fn stable_genuine_function_manifest_hash(
    lift: &GenuineLiftAuthority,
    layout: &GenuineFunctionLayout,
    blocks: &[GenuineLiftedBlock],
    successor_manifest: &[Vec<u64>],
) -> u64 {
    fn update(hash: &mut u64, bytes: &[u8]) {
        for byte in bytes {
            *hash ^= u64::from(*byte);
            *hash = hash.wrapping_mul(0x100000001b3);
        }
        *hash ^= 0xff;
        *hash = hash.wrapping_mul(0x100000001b3);
    }
    let mut hash = 0xcbf29ce484222325;
    update(
        &mut hash,
        &GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION.to_le_bytes(),
    );
    update(&mut hash, &lift.manifest_hash().to_le_bytes());
    update(&mut hash, layout.revision_identity());
    update(&mut hash, &layout.entry_addr().to_le_bytes());
    for (block, successors) in blocks.iter().zip(successor_manifest) {
        update(&mut hash, &block.block.addr.to_le_bytes());
        update(&mut hash, &block.block.size.to_le_bytes());
        update(&mut hash, block.source_bytes());
        for span in block.instruction_spans() {
            update(&mut hash, &span.addr().to_le_bytes());
            update(&mut hash, &span.size().to_le_bytes());
            update(&mut hash, &span.first_canonical_op().to_le_bytes());
            update(&mut hash, &span.canonical_op_count().to_le_bytes());
        }
        for successor in successors {
            update(&mut hash, &successor.to_le_bytes());
        }
    }
    for target in layout.external_exits() {
        update(&mut hash, &target.to_le_bytes());
    }
    hash
}

fn stable_lift_manifest_hash(sla_bytes: &[u8], pspec: &str, arch_name: &str) -> u64 {
    fn update(hash: &mut u64, bytes: &[u8]) {
        for byte in bytes {
            *hash ^= u64::from(*byte);
            *hash = hash.wrapping_mul(0x100000001b3);
        }
        *hash ^= 0xff;
        *hash = hash.wrapping_mul(0x100000001b3);
    }
    let mut hash = 0xcbf29ce484222325;
    update(
        &mut hash,
        &GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION.to_le_bytes(),
    );
    update(&mut hash, sla_bytes);
    update(&mut hash, pspec.as_bytes());
    update(&mut hash, arch_name.as_bytes());
    hash
}

/// Precision profile for lift-time semantic metadata inference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum SemanticMetadataPrecision {
    /// Conservative high-confidence rules only.
    #[default]
    High,
}

/// Options that control semantic metadata generation during lifting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SemanticMetadataOptions {
    /// Enable or disable semantic metadata inference.
    pub enabled: bool,
    /// Inference profile. Phase 1 supports only high precision.
    pub precision: SemanticMetadataPrecision,
}

impl Default for SemanticMetadataOptions {
    fn default() -> Self {
        Self {
            enabled: true,
            precision: SemanticMetadataPrecision::High,
        }
    }
}

/// Wrapper for libsla PcodeInstruction that implements PcodeSource.
struct DisasmInstructionWrapper<'a> {
    instr: &'a PcodeInstruction,
    disasm: &'a Disassembler,
}

impl<'a> PcodeSource for DisasmInstructionWrapper<'a> {
    fn output(&self) -> Option<Varnode> {
        // translate_pcode_op validates every operand before creating this view.
        self.instr
            .output
            .as_ref()
            .and_then(|v| self.disasm.translate_varnode(v).ok())
    }

    fn input(&self, idx: usize) -> Option<Varnode> {
        // translate_pcode_op validates every operand before creating this view.
        self.instr
            .inputs
            .get(idx)
            .and_then(|v| self.disasm.translate_varnode(v).ok())
    }

    fn input_raw_offset(&self, idx: usize) -> Option<u64> {
        self.instr.inputs.get(idx).map(|v| v.address.offset)
    }

    fn input_count(&self) -> usize {
        self.instr.inputs.len()
    }

    fn space_from_index(&self, idx: u64) -> Option<SpaceId> {
        usize::try_from(idx)
            .ok()
            .and_then(|idx| self.disasm.space_map.get(&AddressSpaceId::new(idx)))
            .copied()
    }
}

fn translate_err(e: translate::TranslateError) -> LiftError {
    match e {
        translate::TranslateError::MissingOutput(op) => {
            LiftError::Parse(format!("{} requires output", op))
        }
        translate::TranslateError::MissingInput(op, idx) => {
            LiftError::Parse(format!("{} requires input at index {}", op, idx))
        }
        translate::TranslateError::InvalidSpace(idx) => {
            LiftError::Parse(format!("Invalid space index: {}", idx))
        }
    }
}

fn build_register_name_map(sleigh: &GhidraSleigh) -> HashMap<(u64, u32), String> {
    let mut candidates: HashMap<(u64, u32), Vec<String>> = HashMap::new();

    for (varnode, name) in sleigh.register_name_map() {
        let key = (varnode.address.offset, varnode.size as u32);
        candidates.entry(key).or_default().push(name);
    }

    let mut map = HashMap::new();
    for (key, names) in candidates {
        if let Some(name) = select_register_name(names.iter().map(String::as_str)) {
            map.insert(key, name);
        }
    }

    map
}

impl Disassembler {
    fn from_sla_parts(
        sla_bytes: &[u8],
        pspec: &str,
        arch_name: &str,
        trusted_profile: Option<TrustedSleighProfile>,
    ) -> Result<Self> {
        let sleigh = GhidraSleigh::builder()
            .processor_spec(pspec)
            .map_err(|e| LiftError::Parse(format!("Invalid processor spec: {}", e)))?
            .build(sla_bytes)
            .map_err(|e| LiftError::Parse(format!("Failed to load .sla: {}", e)))?;

        let reg_name_map = build_register_name_map(&sleigh);
        let extracted = crate::sleigh::extract_architecture(&sleigh, arch_name)?;
        let arch = Arc::new(extracted.arch);
        let genuine_authority = trusted_profile.map(|_| {
            GenuineLiftAuthority::new(
                Arc::from(sla_bytes),
                Arc::from(pspec),
                Arc::from(arch_name),
                Arc::clone(&arch),
            )
        });

        Ok(Self {
            program_counter: program_counter_from_pspec(pspec),
            sleigh,
            arch_name: arch_name.to_string(),
            reg_name_map,
            space_map: extracted.space_map,
            genuine_authority,
            trusted_profile,
        })
    }

    /// Construct from a pinned, embedded processor specification.
    ///
    /// This is the only constructor that can mint genuine lift authority.
    pub fn from_trusted_profile(profile: TrustedSleighProfile) -> Result<Self> {
        let (sla_bytes, pspec, arch_name) = profile.specification();
        Self::from_sla_parts(sla_bytes, pspec, arch_name, Some(profile))
    }

    /// The one loaded instance of an embedded profile, loaded on first ask.
    ///
    /// Building a disassembler parses the whole compiled `.sla` and rebuilds
    /// the register and address-space tables from it. Measured on the x86-64
    /// profile: 58 to 91 milliseconds to load, against 21 to 83 *micro*seconds
    /// to lift a three-byte block. Every capture used to pay that once for the
    /// function asked for and once for each callee beside it, so a request with
    /// three callees spent about a quarter of a second loading four identical
    /// copies of one specification, and a twelve-byte import thunk -- which is
    /// most of what an analysis sweep proves -- cost a profile load and almost
    /// nothing else. That is where the per-function cost was.
    ///
    /// Reuse across functions is the same reuse that already happens across
    /// blocks: `lift_genuine_block` takes `&self` and every block of a function
    /// already goes through one instance, at arbitrary addresses and in
    /// arbitrary order. Nothing is reset between them now and nothing was
    /// before.
    ///
    /// Thread-local rather than global, because the instance owns a C++ Sleigh
    /// object that declares neither `Send` nor `Sync`; a thread that lifts gets
    /// its own, which is one per embedded profile per lifting thread. The bound
    /// is the number of profiles the build embeds, at most eleven and in
    /// practice one.
    fn shared_trusted_profile(profile: TrustedSleighProfile) -> Result<Rc<Self>> {
        thread_local! {
            static LOADED: RefCell<HashMap<TrustedSleighProfile, Rc<Disassembler>>> =
                RefCell::new(HashMap::new());
        }
        if let Some(loaded) = LOADED.with(|cache| cache.borrow().get(&profile).map(Rc::clone)) {
            return Ok(loaded);
        }
        // Built outside the borrow: loading is fallible and can itself reach
        // this function for another profile.
        let loaded = Rc::new(Self::from_trusted_profile(profile)?);
        LOADED.with(|cache| {
            cache.borrow_mut().insert(profile, Rc::clone(&loaded));
        });
        Ok(loaded)
    }

    /// Lift every byte of one opaque source capture with the one exact embedded
    /// profile selected by its owned machine tuple.
    pub fn lift_owned_function(source: OwnedFunctionSnapshot) -> Result<TrustedLiftedFunction> {
        let profile = TrustedSleighProfile::from_machine(source.machine())?;
        let disassembler = Self::shared_trusted_profile(profile)?;
        if disassembler.trusted_profile != Some(profile) {
            return Err(LiftError::Unsupported(
                "trusted profile identity was lost while loading Sleigh".to_string(),
            ));
        }
        let trusted_arch = disassembler
            .genuine_authority
            .as_ref()
            .map(GenuineLiftAuthority::arch_spec)
            .ok_or_else(|| {
                LiftError::Unsupported(
                    "trusted lift lost its exact architecture authority".to_string(),
                )
            })?;
        // The capture's carriers are restated in this architecture's numbering
        // before anything reads them, including the agreement check below.
        let source = arch_resolved_source(source, trusted_arch)?;
        // Lifting is a function of the machine tuple and the image bytes; the
        // function interface is evidence about the ABI and is never read below.
        // An absent interface is therefore a fact about the source, not a lift
        // failure, and the obligations that depend on it residualize downstream
        // instead of suppressing the whole function.
        //
        // A present interface must still agree with the machine that was
        // actually lifted, because an interface contradicting the machine is
        // wrong rather than merely missing. Agreement between the interface and
        // the captured field flags is already an invariant established when the
        // snapshot is constructed, so it is not re-checked here.
        if let Some(interface) = source.function_interface()
            && (!captured_frame_pointer_storage_matches_arch(interface, trusted_arch)
                || !captured_return_mechanism_matches_arch(interface, trusted_arch))
        {
            return Err(LiftError::Unsupported(
                "captured frame/return mechanism conflicts with the exact lifted machine"
                    .to_string(),
            ));
        }
        let mut ranges = Vec::with_capacity(source.image().blocks().len());
        let mut blocks = Vec::with_capacity(source.image().blocks().len());
        for block in source.image().blocks() {
            let size = u32::try_from(block.bytes().len()).map_err(|_| {
                LiftError::Parse("owned source block exceeds r2il size range".to_string())
            })?;
            ranges.push(GenuineFunctionBlockRange::new(block.address(), size));
            let mut lifted_block = disassembler.lift_genuine_block(
                block.bytes(),
                block.address(),
                block.bytes().len(),
            )?;
            // radare2 resolves jump tables, and the snapshot carries what it
            // found as switch-case successors. Lifting reads only the bytes, so
            // without this the dispatch arrives as an indirect branch with no
            // targets and the renderer says so and drops the rest of the
            // function: `murmur3_32` rendered four statements of thirty-five and
            // no return at all, because its tail switch on `len & 3` was thrown
            // away between the snapshot and the lift.
            if let Some(switch_addr) = block.switch_instruction() {
                let cases: Vec<r2il::SwitchCase> = block
                    .successors()
                    .iter()
                    .filter(|successor| {
                        successor.kind() == r2source::AdvisorySuccessorKind::SwitchCase
                    })
                    .filter_map(|successor| {
                        successor.case_value().map(|value| r2il::SwitchCase {
                            value,
                            target: successor.target(),
                        })
                    })
                    .collect();
                if !cases.is_empty() {
                    let default_target = block
                        .successors()
                        .iter()
                        .find(|successor| {
                            successor.kind() == r2source::AdvisorySuccessorKind::SwitchDefault
                        })
                        .map(|successor| successor.target());
                    let min_val = cases.iter().map(|case| case.value).min().unwrap_or(0);
                    let max_val = cases.iter().map(|case| case.value).max().unwrap_or(0);
                    lifted_block.block.switch_info = Some(r2il::SwitchInfo {
                        switch_addr,
                        min_val,
                        max_val,
                        default_target,
                        cases,
                    });
                }
            }
            blocks.push(lifted_block);
        }
        validate_owned_snapshot_cfg(&source, &blocks)?;
        let layout = GenuineFunctionLayout::new(
            source.source_revision_identity(),
            source.image().entry_address(),
            ranges,
            source.image().external_exits().iter().copied(),
        )?;
        let lifted = GenuineLiftedFunction::try_from_layout(layout, blocks)?;
        Ok(TrustedLiftedFunction { source, lifted })
    }

    /// Create an analysis-only disassembler from caller-provided specification bytes.
    ///
    /// This constructor never mints certification authority, even when the
    /// bytes happen to equal an embedded trusted profile. Use
    /// [`Self::from_trusted_profile`] for the certifying path.
    ///
    /// # Arguments
    ///
    /// * `sla_bytes` - The compiled .sla file contents
    /// * `pspec` - The processor specification XML string
    /// * `arch_name` - Name of the architecture
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use r2sleigh_lift::disasm::Disassembler;
    ///
    /// // Using sleigh-config precompiled data
    /// let disasm = Disassembler::from_sla(
    ///     include_bytes!("x86-64.sla"),
    ///     include_str!("x86-64.pspec"),
    ///     "x86-64"
    /// )?;
    /// ```
    pub fn from_sla(sla_bytes: &[u8], pspec: &str, arch_name: &str) -> Result<Self> {
        Self::from_sla_parts(sla_bytes, pspec, arch_name, None)
    }

    /// Get the architecture name.
    pub fn arch_name(&self) -> &str {
        &self.arch_name
    }

    /// The register this processor uses as its program counter.
    ///
    /// Taken from the processor spec rather than assumed, because it is `RIP`
    /// on x86-64, `EIP` on x86 and 16-bit, and `pc` on ARM, MIPS and RISC-V.
    /// Writing a branch target to the wrong name leaves the branch with no
    /// effect at all.
    pub fn program_counter(&self) -> &str {
        &self.program_counter
    }

    /// Get the default code address space.
    pub fn default_code_space(&self) -> AddressSpace {
        self.sleigh.default_code_space()
    }

    /// List all address spaces.
    pub fn address_spaces(&self) -> Vec<AddressSpace> {
        self.sleigh.address_spaces()
    }

    /// Get a register's varnode data by name.
    pub fn register(&self, name: &str) -> Result<VarnodeData> {
        self.sleigh
            .register_from_name(name)
            .map_err(|e| LiftError::Parse(format!("Unknown register '{}': {}", name, e)))
    }

    /// Get the register name for a varnode in the register space.
    ///
    /// Returns `None` if the varnode is not in the register space or if
    /// no register name is found for the given offset and size.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let vn = Varnode::register(0x20, 8); // RSP on x86-64
    /// let name = disasm.register_name(&vn);
    /// assert_eq!(name, Some("RSP".to_string()));
    /// ```
    pub fn register_name(&self, vn: &Varnode) -> Option<String> {
        if vn.space != SpaceId::Register {
            return None;
        }

        if let Some(name) = self.reg_name_map.get(&(vn.offset, vn.size)) {
            return Some(name.clone());
        }

        // Get the register address space
        let reg_space = self.sleigh.address_space_by_name("register")?;

        // Create a VarnodeData to query libsla
        let varnode_data = VarnodeData::new(Address::new(reg_space, vn.offset), vn.size as usize);

        self.sleigh.register_name(&varnode_data)
    }

    /// Format a varnode as a human-readable string, resolving register names.
    ///
    /// This is useful for pretty-printing P-code operations.
    pub fn format_varnode(&self, vn: &Varnode) -> String {
        match vn.space {
            SpaceId::Const => format!("0x{:x}", vn.offset),
            SpaceId::Register => {
                // Try to resolve the register name
                if let Some(name) = self.register_name(vn) {
                    name
                } else {
                    format!("reg:0x{:x}:{}", vn.offset, vn.size)
                }
            }
            SpaceId::Unique => format!("tmp:0x{:x}", vn.offset),
            SpaceId::Ram => format!("[0x{:x}]:{}", vn.offset, vn.size),
            SpaceId::Custom(n) => format!("space{}:0x{:x}", n, vn.offset),
        }
    }

    /// Disassemble instruction bytes at a given address and return r2il.
    ///
    /// # Arguments
    ///
    /// * `bytes` - Instruction bytes to disassemble
    /// * `addr` - Address where the instruction is located
    ///
    /// # Returns
    ///
    /// An `R2ILBlock` containing the translated operations, or an error.
    ///
    /// Note: This lifts a **single instruction**. Use `lift_block` to lift
    /// multiple instructions within a basic block.
    pub fn lift(&self, bytes: &[u8], addr: u64) -> Result<R2ILBlock> {
        self.lift_with_options(bytes, addr, SemanticMetadataOptions::default())
    }

    /// Lift a single instruction with explicit semantic metadata options.
    pub fn lift_with_options(
        &self,
        bytes: &[u8],
        addr: u64,
        options: SemanticMetadataOptions,
    ) -> Result<R2ILBlock> {
        let mut block = self.lift_canonical(bytes, addr)?;
        self.annotate_semantic_metadata(&mut block, options);
        Ok(block)
    }

    /// Translate exactly the Sleigh-produced P-code plus the local label
    /// normalization required to preserve the instruction's control graph.
    /// No mnemonic, user-op name, or inferred metadata participates.
    fn lift_canonical(&self, bytes: &[u8], addr: u64) -> Result<R2ILBlock> {
        let code_space = self.sleigh.default_code_space();
        let address = Address::new(code_space, addr);

        // Create an instruction loader from the bytes
        let loader = ByteLoader::new(bytes, addr);

        // Disassemble to P-code
        let pcode = self
            .sleigh
            .disassemble_pcode(&loader, address)
            .map_err(|e| {
                LiftError::Pcode(crate::pcode::PcodeError::InvalidOpcode(format!(
                    "Disassembly failed: {}",
                    e
                )))
            })?;

        // Translate P-code to r2il
        let mut block = self.translate_pcode(pcode, addr)?;
        crate::internal_control::normalize_instruction_local_control(&mut block);
        Ok(block)
    }

    /// Minimum bytes required by libsla for disassembly.
    const MIN_BYTES: usize = 16;

    /// Lift an entire basic block (multiple instructions) to r2il.
    ///
    /// # Arguments
    ///
    /// * `bytes` - Instruction bytes for the entire block (should be at least 16 bytes for libsla)
    /// * `addr` - Starting address of the block
    /// * `block_size` - Size of the block in bytes
    ///
    /// # Returns
    ///
    /// An `R2ILBlock` containing operations from all instructions in the block.
    pub fn lift_block(&self, bytes: &[u8], addr: u64, block_size: usize) -> Result<R2ILBlock> {
        self.lift_block_with_options(bytes, addr, block_size, SemanticMetadataOptions::default())
    }

    /// Lift a basic block with explicit semantic metadata options.
    pub fn lift_block_with_options(
        &self,
        bytes: &[u8],
        addr: u64,
        block_size: usize,
        options: SemanticMetadataOptions,
    ) -> Result<R2ILBlock> {
        self.lift_block_with_policy_and_spans(bytes, addr, block_size, Some(options))
            .map(|(block, _)| block)
    }

    fn lift_block_with_policy_and_spans(
        &self,
        bytes: &[u8],
        addr: u64,
        block_size: usize,
        enrichment: Option<SemanticMetadataOptions>,
    ) -> Result<(R2ILBlock, Vec<GenuineInstructionSpan>)> {
        let block_size_u32 = u32::try_from(block_size)
            .map_err(|_| LiftError::Parse("block size exceeds r2il range".to_string()))?;
        let mut combined_block = R2ILBlock::new(addr, block_size_u32);
        let mut instruction_spans = Vec::new();
        let mut offset = 0usize;

        while offset < block_size {
            let remaining = &bytes[offset..];
            if remaining.is_empty() {
                break;
            }

            let offset_u64 = u64::try_from(offset)
                .map_err(|_| LiftError::Parse("instruction offset exceeds u64".to_string()))?;
            let instr_addr = addr
                .checked_add(offset_u64)
                .ok_or_else(|| LiftError::Parse("instruction address overflows".to_string()))?;

            // libsla requires at least 16 bytes; pad if necessary
            let lift_bytes: Vec<u8> = if remaining.len() < Self::MIN_BYTES {
                let mut padded = remaining.to_vec();
                padded.resize(Self::MIN_BYTES, 0);
                padded
            } else {
                remaining.to_vec()
            };

            // Lift single instruction
            let lifted = match enrichment {
                Some(options) => self.lift_with_options(&lift_bytes, instr_addr, options),
                None => self.lift_canonical(&lift_bytes, instr_addr),
            };
            match lifted {
                Ok(instr_block) => {
                    let R2ILBlock {
                        size: instr_size_u32,
                        ops,
                        op_metadata,
                        ..
                    } = instr_block;
                    let instr_size = instr_size_u32 as usize;
                    if instr_size == 0 {
                        // Prevent infinite loop on zero-size instruction
                        break;
                    }
                    let base_op_index = combined_block.ops.len();
                    let canonical_op_count = ops.len();
                    let first_canonical_op = u64::try_from(base_op_index).map_err(|_| {
                        LiftError::Parse("canonical P-code index exceeds u64".to_string())
                    })?;
                    let canonical_op_count = u64::try_from(canonical_op_count).map_err(|_| {
                        LiftError::Parse("canonical P-code count exceeds u64".to_string())
                    })?;
                    instruction_spans.push(GenuineInstructionSpan {
                        addr: instr_addr,
                        size: instr_size_u32,
                        first_canonical_op,
                        canonical_op_count,
                    });

                    let mut instr_op_metadata = op_metadata;
                    // Append all ops from this instruction
                    for op in ops {
                        combined_block.push(op);
                    }
                    for local_idx in 0..(combined_block.ops.len() - base_op_index) {
                        let mut meta = instr_op_metadata.remove(&local_idx).unwrap_or_default();
                        meta.instruction_addr = Some(instr_addr);
                        combined_block.set_op_metadata(base_op_index + local_idx, meta);
                    }

                    offset += instr_size;
                }
                Err(error) if enrichment.is_none() => return Err(error),
                Err(_) => {
                    // Stop on disassembly error (e.g., invalid instruction)
                    break;
                }
            }
        }

        // Update the block size to reflect actual bytes consumed
        combined_block.size = u32::try_from(offset)
            .map_err(|_| LiftError::Parse("lifted block size exceeds r2il range".to_string()))?;

        Ok((combined_block, instruction_spans))
    }

    /// Lift one complete block and retain unforgeable, immutable origin.
    pub fn lift_genuine_block(
        &self,
        bytes: &[u8],
        addr: u64,
        block_size: usize,
    ) -> Result<GenuineLiftedBlock> {
        if block_size == 0 || block_size > bytes.len() {
            return Err(LiftError::Parse(
                "genuine lift requires a nonempty in-bounds block".to_string(),
            ));
        }
        let authority = self.genuine_authority.clone().ok_or_else(|| {
            LiftError::Unsupported(
                "genuine lift requires an embedded trusted Sleigh profile".to_string(),
            )
        })?;
        let (block, instruction_spans) =
            self.lift_block_with_policy_and_spans(bytes, addr, block_size, None)?;
        if usize::try_from(block.size) != Ok(block_size) {
            return Err(LiftError::Parse(format!(
                "genuine lift consumed {} of {block_size} requested bytes",
                block.size
            )));
        }
        Ok(GenuineLiftedBlock {
            authority,
            block,
            source_bytes: Arc::from(&bytes[..block_size]),
            instruction_spans: instruction_spans.into(),
        })
    }

    /// Disassemble and get native assembly mnemonic.
    pub fn disasm_native(&self, bytes: &[u8], addr: u64) -> Result<(String, usize)> {
        let code_space = self.sleigh.default_code_space();
        let address = Address::new(code_space, addr);
        let loader = ByteLoader::new(bytes, addr);

        let native = self
            .sleigh
            .disassemble_native(&loader, address)
            .map_err(|e| LiftError::Parse(format!("Disassembly failed: {}", e)))?;

        let mnemonic = format!(
            "{} {}",
            native.instruction.mnemonic, native.instruction.body
        );
        let size = native.origin.size;

        Ok((mnemonic.trim().to_string(), size))
    }

    /// Translate a P-code disassembly to an r2il block.
    fn translate_pcode(&self, pcode: PcodeDisassembly, addr: u64) -> Result<R2ILBlock> {
        let instr_size = pcode.origin.size as u32;
        let mut block = R2ILBlock::new(addr, instr_size);

        let mut ops = Vec::with_capacity(pcode.instructions.len());
        for pcode_instr in pcode.instructions {
            if let Some(op) = self.translate_pcode_op(&pcode_instr)? {
                ops.push(op);
            }
        }

        // Where an expansion's own temporaries may live: above every temporary
        // this instruction already uses. Sleigh scopes the unique space to the
        // instruction, so that is the whole extent an expansion has to stay
        // clear of, and taking it from the instruction itself means there is no
        // offset to guess and nothing to collide with.
        let temp_base = ops
            .iter()
            .flat_map(|op| op.output().into_iter().chain(op.inputs()))
            .filter(|varnode| varnode.space == SpaceId::Unique)
            .filter_map(|varnode| varnode.offset.checked_add(u64::from(varnode.size)))
            .max()
            .unwrap_or(0);

        // A trap ends the instruction. Sleigh writes `brk` as a user operation
        // that produces `pc` followed by a branch through it, so the branch's
        // only definition of its target is the trap itself; expanding the trap
        // into `Breakpoint`, which produces nothing, would leave that branch
        // reading a `pc` nothing defines. Control does not reach it either way
        // -- the exception is taken at the trap and does not come back -- so
        // the operations Sleigh writes after it in the same instruction are not
        // executed, and dropping them is what the machine does.
        for op in ops {
            for expanded in self.expand_user_operation(op, temp_base) {
                let traps = matches!(expanded, R2ILOp::Breakpoint);
                block.push(expanded);
                if traps {
                    return Ok(block);
                }
            }
        }

        Ok(block)
    }

    fn annotate_semantic_metadata(&self, block: &mut R2ILBlock, options: SemanticMetadataOptions) {
        // Inference runs against an analysis copy so advisory varnode hints can
        // contribute to out-of-band op metadata without altering canonical
        // Sleigh operations or operands.
        let mut analysis = block.clone();
        annotate_semantic_metadata_with_hints(&mut analysis, &self.arch_name, options, |vn| {
            self.register_name(vn)
        });
        block.op_metadata = analysis.op_metadata;
    }

    /// Translate a single P-code instruction to an r2il operation.
    /// The name the architecture gives the user-defined operation at `index`.
    fn user_op_name(&self, index: u32) -> Option<&str> {
        self.genuine_authority
            .as_ref()?
            .arch_spec()
            .user_ops
            .get(index as usize)
            .map(String::as_str)
    }

    /// Give a user-defined operation its semantics, where the architecture
    /// names one this lift models.
    ///
    /// A `CallOther` carries no semantics at all, so everything downstream can
    /// only refuse the instruction and, with it, the function. Where the
    /// operation's meaning is exactly expressible in the ordinary vocabulary,
    /// expanding it here is what keeps the rest of the pipeline free of any
    /// vector-specific machinery. An operation this does not model is returned
    /// untouched and still refuses, which is the honest answer.
    fn expand_user_operation(&self, op: R2ILOp, temp_base: u64) -> Vec<R2ILOp> {
        let R2ILOp::CallOther {
            userop,
            output,
            inputs,
        } = &op
        else {
            return vec![op];
        };
        let expanded = match self.user_op_name(*userop) {
            Some("NEON_ext") => Self::expand_neon_ext(output.as_ref(), inputs, temp_base),
            Some("NEON_ushl") => Self::expand_neon_ushl(output.as_ref(), inputs, temp_base),
            // A trap, and the pipeline already has one. `R2ILOp::Breakpoint` is
            // seeded as `Kind::Trap` by the obligation ledger, which is exactly
            // what these are: control leaves for an exception handler and does
            // not come back. Sleigh models that as a user-operation writing
            // `pc`, which nothing downstream could project, so the whole
            // function refused.
            //
            // The trap code -- `brk 0xc471`'s immediate, say -- is dropped,
            // because `R2ILOp::Breakpoint` carries no operands. It identifies
            // which check failed and is still in the disassembly; what matters
            // for rendering is that control stops here, and that is preserved
            // exactly.
            Some("SoftwareBreakpoint") | Some("UndefinedInstructionException") => {
                Some(vec![R2ILOp::Breakpoint])
            }
            _ => None,
        };
        expanded.unwrap_or_else(|| vec![op])
    }

    /// `NEON_ext(rn, rm, index, element_size)` -- AArch64 `EXT`.
    ///
    /// The result is the vector's width of bytes taken from the concatenation
    /// of `rm` above `rn`, starting at byte `index`. As a whole-register value
    /// that is `rn` shifted down by `index` bytes with `rm` shifted up into the
    /// space it vacated.
    ///
    /// Only the byte-granular form is expanded, which is the only form the
    /// specification uses; anything else is left to refuse.
    fn expand_neon_ext(
        output: Option<&Varnode>,
        inputs: &[Varnode],
        temp_base: u64,
    ) -> Option<Vec<R2ILOp>> {
        let [rn, rm, index, element_size] = inputs else {
            return None;
        };
        let output = output?;
        if index.space != SpaceId::Const
            || element_size.space != SpaceId::Const
            || element_size.offset != 1
        {
            return None;
        }
        let width_bytes = u64::from(output.size);
        if output.size != rn.size || output.size != rm.size || width_bytes == 0 {
            return None;
        }
        let taken = index.offset;
        if taken == 0 {
            return Some(vec![R2ILOp::Copy {
                dst: output.clone(),
                src: rn.clone(),
            }]);
        }
        if taken >= width_bytes {
            return None;
        }
        let low = Varnode::unique(temp_base, output.size);
        let high = Varnode::unique(temp_base.checked_add(width_bytes)?, output.size);
        let down = Varnode::constant(taken * 8, output.size);
        let up = Varnode::constant((width_bytes - taken) * 8, output.size);
        Some(vec![
            R2ILOp::IntRight {
                dst: low.clone(),
                a: rn.clone(),
                b: down,
            },
            R2ILOp::IntLeft {
                dst: high.clone(),
                a: rm.clone(),
                b: up,
            },
            R2ILOp::IntOr {
                dst: output.clone(),
                a: low,
                b: high,
            },
        ])
    }

    /// `NEON_ushl(rn, rm, element_size)` -- AArch64 `USHL`.
    ///
    /// Each element of the result is the corresponding element of `rn` shifted
    /// by the signed low byte of the corresponding element of `rm`: left when
    /// that byte is positive, right when it is negative, and zero when the
    /// distance reaches the element's width, which is what the architecture
    /// says and not what a C shift would do.
    ///
    /// Written out per element and recomposed, because the element is where the
    /// operation is defined; nothing downstream needs to know it came from a
    /// vector.
    fn expand_neon_ushl(
        output: Option<&Varnode>,
        inputs: &[Varnode],
        temp_base: u64,
    ) -> Option<Vec<R2ILOp>> {
        let [rn, rm, element_size] = inputs else {
            return None;
        };
        let output = output?;
        if element_size.space != SpaceId::Const {
            return None;
        }
        let lane_bytes = u32::try_from(element_size.offset).ok()?;
        if lane_bytes == 0
            || output.size != rn.size
            || output.size != rm.size
            || output.size % lane_bytes != 0
        {
            return None;
        }
        let lanes = output.size / lane_bytes;
        if lanes < 2 || !lanes.is_power_of_two() {
            return None;
        }
        let lane_bits = u64::from(lane_bytes).checked_mul(8)?;

        let mut ops = Vec::new();
        let mut next = temp_base;
        let temp = |size: u32, next: &mut u64| {
            let node = Varnode::unique(*next, size);
            *next += u64::from(size).max(1);
            node
        };

        let mut lane_values = Vec::with_capacity(lanes as usize);
        for lane in 0..lanes {
            let byte_offset = lane * lane_bytes;
            let value = temp(lane_bytes, &mut next);
            ops.push(R2ILOp::Subpiece {
                dst: value.clone(),
                src: rn.clone(),
                offset: byte_offset,
            });
            let distance_lane = temp(lane_bytes, &mut next);
            ops.push(R2ILOp::Subpiece {
                dst: distance_lane.clone(),
                src: rm.clone(),
                offset: byte_offset,
            });
            // The distance is the element's low byte, read as signed.
            let distance_byte = temp(1, &mut next);
            ops.push(R2ILOp::Subpiece {
                dst: distance_byte.clone(),
                src: distance_lane,
                offset: 0,
            });
            let distance = temp(lane_bytes, &mut next);
            ops.push(R2ILOp::IntSExt {
                dst: distance.clone(),
                src: distance_byte,
            });

            let zero = Varnode::constant(0, lane_bytes);
            let negative = temp(1, &mut next);
            ops.push(R2ILOp::IntSLess {
                dst: negative.clone(),
                a: distance.clone(),
                b: zero.clone(),
            });
            let magnitude = temp(lane_bytes, &mut next);
            ops.push(R2ILOp::IntSub {
                dst: magnitude.clone(),
                a: zero.clone(),
                b: distance.clone(),
            });

            let left = temp(lane_bytes, &mut next);
            ops.push(R2ILOp::IntLeft {
                dst: left.clone(),
                a: value.clone(),
                b: distance.clone(),
            });
            let right = temp(lane_bytes, &mut next);
            ops.push(R2ILOp::IntRight {
                dst: right.clone(),
                a: value,
                b: magnitude.clone(),
            });
            let shifted = temp(lane_bytes, &mut next);
            ops.push(R2ILOp::Select {
                dst: shifted.clone(),
                cond: negative.clone(),
                if_true: right,
                if_false: left,
            });

            // A distance at or beyond the element's width leaves zero, in both
            // directions. A C shift would be undefined there, so it is decided
            // here rather than left to the rendering.
            let distance_magnitude = temp(lane_bytes, &mut next);
            ops.push(R2ILOp::Select {
                dst: distance_magnitude.clone(),
                cond: negative,
                if_true: magnitude,
                if_false: distance,
            });
            let within = temp(1, &mut next);
            ops.push(R2ILOp::IntLess {
                dst: within.clone(),
                a: distance_magnitude,
                b: Varnode::constant(lane_bits, lane_bytes),
            });
            let result = temp(lane_bytes, &mut next);
            ops.push(R2ILOp::Select {
                dst: result.clone(),
                cond: within,
                if_true: shifted,
                if_false: zero,
            });
            lane_values.push(result);
        }

        // Recompose, halving the count each round until one value is left.
        let mut width = lane_bytes;
        while lane_values.len() > 1 {
            let mut joined = Vec::with_capacity(lane_values.len() / 2);
            for pair in lane_values.chunks(2) {
                let [low, high] = pair else {
                    return None;
                };
                let wider = temp(width * 2, &mut next);
                ops.push(R2ILOp::Piece {
                    dst: wider.clone(),
                    hi: high.clone(),
                    lo: low.clone(),
                });
                joined.push(wider);
            }
            lane_values = joined;
            width *= 2;
        }
        let composed = lane_values.pop()?;
        ops.push(R2ILOp::Copy {
            dst: output.clone(),
            src: composed,
        });
        Some(ops)
    }

    fn translate_pcode_op(&self, instr: &PcodeInstruction) -> Result<Option<R2ILOp>> {
        self.validate_pcode_spaces(instr)?;
        let source = DisasmInstructionWrapper {
            instr,
            disasm: self,
        };

        // Helpers for common patterns
        let unary = |name, f: fn(Varnode, Varnode) -> R2ILOp| {
            translate::translate_unary(&source, name, f)
                .map(Some)
                .map_err(translate_err)
        };

        let binary = |name, f: fn(Varnode, Varnode, Varnode) -> R2ILOp| {
            translate::translate_binary(&source, name, f)
                .map(Some)
                .map_err(translate_err)
        };

        match &instr.op_code {
            // Data movement
            OpCode::Copy => {
                let dst = translate::require_output(&source, "COPY").map_err(translate_err)?;
                let src = translate::require_input(&source, 0, "COPY").map_err(translate_err)?;
                // A Sleigh direct-address form writes memory through a
                // RAM-space destination varnode rather than through STORE.
                // Canonicalize it so an observable memory write stays a memory
                // write instead of becoming an SSA value of a register-like RAM
                // location, which would leave the effect uninventoried and turn
                // a later read of the same address into a value phi.
                if dst.space == SpaceId::Ram || src.space == SpaceId::Ram {
                    let address_size = u32::try_from(self.default_code_space().address_size)
                        .map_err(|_| LiftError::Parse("default code space address size".into()))?;
                    if dst.space == SpaceId::Ram {
                        return Ok(Some(R2ILOp::Store {
                            space: SpaceId::Ram,
                            addr: Varnode::constant(dst.offset, address_size),
                            val: src,
                        }));
                    }
                    return Ok(Some(R2ILOp::Load {
                        dst,
                        space: SpaceId::Ram,
                        addr: Varnode::constant(src.offset, address_size),
                    }));
                }
                Ok(Some(R2ILOp::Copy { dst, src }))
            }

            OpCode::Load => translate::translate_load(&source)
                .map(Some)
                .map_err(translate_err),

            OpCode::Store => translate::translate_store(&source)
                .map(Some)
                .map_err(translate_err),

            // Control flow
            OpCode::Branch => {
                let target =
                    translate::require_input(&source, 0, "BRANCH").map_err(translate_err)?;
                Ok(Some(R2ILOp::Branch { target }))
            }

            OpCode::BranchConditional => translate::translate_cbranch(&source)
                .map(Some)
                .map_err(translate_err),

            OpCode::BranchIndirect => {
                let target =
                    translate::require_input(&source, 0, "BRANCHIND").map_err(translate_err)?;
                Ok(Some(R2ILOp::BranchInd { target }))
            }

            OpCode::Call => {
                let target = translate::require_input(&source, 0, "CALL").map_err(translate_err)?;
                Ok(Some(R2ILOp::Call { target }))
            }

            OpCode::CallIndirect => {
                let target =
                    translate::require_input(&source, 0, "CALLIND").map_err(translate_err)?;
                Ok(Some(R2ILOp::CallInd { target }))
            }

            OpCode::Return => {
                let target =
                    translate::require_input(&source, 0, "RETURN").map_err(translate_err)?;
                Ok(Some(R2ILOp::Return { target }))
            }

            // Integer arithmetic
            // Integer arithmetic
            OpCode::Int(IntOp::Add) => binary("INT_ADD", |dst, a, b| R2ILOp::IntAdd { dst, a, b }),
            OpCode::Int(IntOp::Subtract) => {
                binary("INT_SUB", |dst, a, b| R2ILOp::IntSub { dst, a, b })
            }
            OpCode::Int(IntOp::Multiply) => {
                binary("INT_MULT", |dst, a, b| R2ILOp::IntMult { dst, a, b })
            }
            OpCode::Int(IntOp::Divide(IntSign::Unsigned)) => {
                binary("INT_DIV", |dst, a, b| R2ILOp::IntDiv { dst, a, b })
            }
            OpCode::Int(IntOp::Divide(IntSign::Signed)) => {
                binary("INT_SDIV", |dst, a, b| R2ILOp::IntSDiv { dst, a, b })
            }
            OpCode::Int(IntOp::Remainder(IntSign::Unsigned)) => {
                binary("INT_REM", |dst, a, b| R2ILOp::IntRem { dst, a, b })
            }
            OpCode::Int(IntOp::Remainder(IntSign::Signed)) => {
                binary("INT_SREM", |dst, a, b| R2ILOp::IntSRem { dst, a, b })
            }
            OpCode::Int(IntOp::Negate) => {
                unary("INT_2COMP", |dst, src| R2ILOp::IntNegate { dst, src })
            }

            // Bitwise operations
            OpCode::Int(IntOp::Bitwise(BoolOp::And)) => {
                binary("INT_AND", |dst, a, b| R2ILOp::IntAnd { dst, a, b })
            }
            OpCode::Int(IntOp::Bitwise(BoolOp::Or)) => {
                binary("INT_OR", |dst, a, b| R2ILOp::IntOr { dst, a, b })
            }
            OpCode::Int(IntOp::Bitwise(BoolOp::Xor)) => {
                binary("INT_XOR", |dst, a, b| R2ILOp::IntXor { dst, a, b })
            }
            OpCode::Int(IntOp::Bitwise(BoolOp::Negate)) => {
                unary("INT_NEGATE", |dst, src| R2ILOp::IntNot { dst, src })
            }

            // Shift operations
            OpCode::Int(IntOp::ShiftLeft) => {
                binary("INT_LEFT", |dst, a, b| R2ILOp::IntLeft { dst, a, b })
            }
            OpCode::Int(IntOp::ShiftRight(IntSign::Unsigned)) => {
                binary("INT_RIGHT", |dst, a, b| R2ILOp::IntRight { dst, a, b })
            }
            OpCode::Int(IntOp::ShiftRight(IntSign::Signed)) => {
                binary("INT_SRIGHT", |dst, a, b| R2ILOp::IntSRight { dst, a, b })
            }

            // Comparison operations
            OpCode::Int(IntOp::Equal) => {
                binary("INT_EQUAL", |dst, a, b| R2ILOp::IntEqual { dst, a, b })
            }
            OpCode::Int(IntOp::NotEqual) => binary("INT_NOTEQUAL", |dst, a, b| {
                R2ILOp::IntNotEqual { dst, a, b }
            }),
            OpCode::Int(IntOp::LessThan(IntSign::Unsigned)) => {
                binary("INT_LESS", |dst, a, b| R2ILOp::IntLess { dst, a, b })
            }
            OpCode::Int(IntOp::LessThan(IntSign::Signed)) => {
                binary("INT_SLESS", |dst, a, b| R2ILOp::IntSLess { dst, a, b })
            }

            OpCode::Int(IntOp::LessThanOrEqual(IntSign::Unsigned)) => {
                binary("INT_LESSEQUAL", |dst, a, b| R2ILOp::IntLessEqual {
                    dst,
                    a,
                    b,
                })
            }

            OpCode::Int(IntOp::LessThanOrEqual(IntSign::Signed)) => {
                binary("INT_SLESSEQUAL", |dst, a, b| R2ILOp::IntSLessEqual {
                    dst,
                    a,
                    b,
                })
            }

            // Extension operations
            OpCode::Int(IntOp::Extension(IntSign::Unsigned)) => {
                unary("INT_ZEXT", |dst, src| R2ILOp::IntZExt { dst, src })
            }

            OpCode::Int(IntOp::Extension(IntSign::Signed)) => {
                unary("INT_SEXT", |dst, src| R2ILOp::IntSExt { dst, src })
            }

            // Carry/Borrow
            OpCode::Int(IntOp::Carry(IntSign::Unsigned)) => {
                binary("INT_CARRY", |dst, a, b| R2ILOp::IntCarry { dst, a, b })
            }

            OpCode::Int(IntOp::Carry(IntSign::Signed)) => {
                binary("INT_SCARRY", |dst, a, b| R2ILOp::IntSCarry { dst, a, b })
            }

            OpCode::Int(IntOp::Borrow) => {
                binary("INT_SBORROW", |dst, a, b| R2ILOp::IntSBorrow { dst, a, b })
            }

            // Boolean operations
            OpCode::Bool(BoolOp::And) => {
                binary("BOOL_AND", |dst, a, b| R2ILOp::BoolAnd { dst, a, b })
            }

            OpCode::Bool(BoolOp::Or) => binary("BOOL_OR", |dst, a, b| R2ILOp::BoolOr { dst, a, b }),

            OpCode::Bool(BoolOp::Xor) => {
                binary("BOOL_XOR", |dst, a, b| R2ILOp::BoolXor { dst, a, b })
            }

            OpCode::Bool(BoolOp::Negate) => {
                unary("BOOL_NEGATE", |dst, src| R2ILOp::BoolNot { dst, src })
            }

            // Piece/Subpiece
            // Piece/Subpiece
            OpCode::Piece => binary("PIECE", |dst, hi, lo| R2ILOp::Piece { dst, hi, lo }),

            OpCode::Subpiece => translate::translate_subpiece(&source)
                .map(Some)
                .map_err(translate_err),

            // Popcount/LzCount
            OpCode::Popcount => unary("POPCOUNT", |dst, src| R2ILOp::PopCount { dst, src }),

            OpCode::LzCount => unary("LZCOUNT", |dst, src| R2ILOp::Lzcount { dst, src }),

            // Floating point operations
            OpCode::Float(FloatOp::Add) => {
                binary("FLOAT_ADD", |dst, a, b| R2ILOp::FloatAdd { dst, a, b })
            }

            OpCode::Float(FloatOp::Subtract) => {
                binary("FLOAT_SUB", |dst, a, b| R2ILOp::FloatSub { dst, a, b })
            }

            OpCode::Float(FloatOp::Multiply) => {
                binary("FLOAT_MULT", |dst, a, b| R2ILOp::FloatMult { dst, a, b })
            }

            OpCode::Float(FloatOp::Divide) => {
                binary("FLOAT_DIV", |dst, a, b| R2ILOp::FloatDiv { dst, a, b })
            }

            OpCode::Float(FloatOp::Negate) => {
                unary("FLOAT_NEG", |dst, src| R2ILOp::FloatNeg { dst, src })
            }

            OpCode::Float(FloatOp::AbsoluteValue) => {
                unary("FLOAT_ABS", |dst, src| R2ILOp::FloatAbs { dst, src })
            }

            OpCode::Float(FloatOp::SquareRoot) => {
                unary("FLOAT_SQRT", |dst, src| R2ILOp::FloatSqrt { dst, src })
            }

            OpCode::Float(FloatOp::Equal) => {
                binary("FLOAT_EQUAL", |dst, a, b| R2ILOp::FloatEqual { dst, a, b })
            }

            OpCode::Float(FloatOp::NotEqual) => binary("FLOAT_NOTEQUAL", |dst, a, b| {
                R2ILOp::FloatNotEqual { dst, a, b }
            }),

            OpCode::Float(FloatOp::LessThan) => {
                binary("FLOAT_LESS", |dst, a, b| R2ILOp::FloatLess { dst, a, b })
            }

            OpCode::Float(FloatOp::LessThanOrEqual) => binary("FLOAT_LESSEQUAL", |dst, a, b| {
                R2ILOp::FloatLessEqual { dst, a, b }
            }),

            OpCode::Float(FloatOp::IsNaN) => {
                unary("FLOAT_NAN", |dst, src| R2ILOp::FloatNaN { dst, src })
            }

            OpCode::Float(FloatOp::IntToFloat) => {
                unary("INT2FLOAT", |dst, src| R2ILOp::Int2Float { dst, src })
            }

            OpCode::Float(FloatOp::FloatToFloat) => {
                unary("FLOAT_FLOAT", |dst, src| R2ILOp::FloatFloat { dst, src })
            }

            OpCode::Float(FloatOp::Truncate) => {
                unary("TRUNC", |dst, src| R2ILOp::Trunc { dst, src })
            }

            OpCode::Float(FloatOp::Ceiling) => {
                unary("FLOAT_CEIL", |dst, src| R2ILOp::FloatCeil { dst, src })
            }

            OpCode::Float(FloatOp::Floor) => {
                unary("FLOAT_FLOOR", |dst, src| R2ILOp::FloatFloor { dst, src })
            }

            OpCode::Float(FloatOp::Round) => {
                unary("FLOAT_ROUND", |dst, src| R2ILOp::FloatRound { dst, src })
            }

            // Pseudo operations
            OpCode::Pseudo(PseudoOp::CallOther) => {
                // CALLOTHER: first input is userop index, rest are arguments
                let userop_vn =
                    translate::require_input(&source, 0, "CALLOTHER").map_err(translate_err)?;
                let userop = u32::try_from(userop_vn.offset).map_err(|_| {
                    LiftError::Unsupported(format!(
                        "Sleigh CALLOTHER id does not fit r2il: {}",
                        userop_vn.offset
                    ))
                })?;
                let output = source.output();

                // Collect remaining inputs (args)
                let mut inputs = Vec::new();
                for i in 1..source.input_count() {
                    if let Some(input) = source.input(i) {
                        inputs.push(input);
                    }
                }

                Ok(Some(R2ILOp::CallOther {
                    userop,
                    output,
                    inputs,
                }))
            }

            OpCode::Pseudo(op) => Err(LiftError::Unsupported(format!(
                "Sleigh pseudo operation {op:?} has no exact r2il semantics"
            ))),
            OpCode::Analysis(op) => Err(LiftError::Unsupported(format!(
                "analysis P-code operation {op:?} is invalid in a machine-code lift"
            ))),
            OpCode::Unknown(raw) => Err(LiftError::Unsupported(format!(
                "unknown Sleigh P-code operation {raw}"
            ))),
        }
    }

    /// Convert a libsla VarnodeData to our Varnode type.
    fn translate_varnode(&self, vn: &VarnodeData) -> Result<Varnode> {
        let space = self.translate_space(&vn.address.address_space)?;
        let size = u32::try_from(vn.size).map_err(|_| {
            LiftError::Unsupported(format!(
                "Sleigh varnode size does not fit r2il: {}",
                vn.size
            ))
        })?;
        Ok(Varnode {
            space,
            offset: vn.address.offset,
            size,
            meta: None,
        })
    }

    fn validate_pcode_spaces(&self, instr: &PcodeInstruction) -> Result<()> {
        self.translate_space(&instr.address.address_space)?;
        for input in &instr.inputs {
            self.translate_varnode(input)?;
        }
        if let Some(output) = &instr.output {
            self.translate_varnode(output)?;
        }
        Ok(())
    }

    /// Convert a libsla AddressSpace using the exact metadata-extraction map.
    fn translate_space(&self, space: &AddressSpace) -> Result<SpaceId> {
        self.space_map.get(&space.id).copied().ok_or_else(|| {
            LiftError::Unsupported(format!(
                "Sleigh emitted unmapped address space '{}' ({})",
                space.name, space.id
            ))
        })
    }
}

/// Simple byte loader for instruction bytes.
struct ByteLoader<'a> {
    bytes: &'a [u8],
    base_addr: u64,
}

impl<'a> ByteLoader<'a> {
    fn new(bytes: &'a [u8], base_addr: u64) -> Self {
        Self { bytes, base_addr }
    }
}

impl<'a> InstructionLoader for ByteLoader<'a> {
    fn load_instruction_bytes(
        &self,
        varnode: &VarnodeData,
    ) -> std::result::Result<Vec<u8>, String> {
        let offset = varnode
            .address
            .offset
            .checked_sub(self.base_addr)
            .ok_or_else(|| "Address underflow".to_string())?;
        let start = offset as usize;
        let end = start
            .checked_add(varnode.size)
            .ok_or_else(|| "Size overflow".to_string())?;

        if end <= self.bytes.len() {
            Ok(self.bytes[start..end].to_vec())
        } else {
            Err(format!(
                "Out of bounds: requested {}..{}, have {}",
                start,
                end,
                self.bytes.len()
            ))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct VnKey {
    space: SpaceId,
    offset: u64,
    size: u32,
}

impl From<&Varnode> for VnKey {
    fn from(vn: &Varnode) -> Self {
        Self {
            space: vn.space,
            offset: vn.offset,
            size: vn.size,
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct InferredSemantics {
    storage_class: Option<StorageClass>,
    pointer_hint: Option<PointerHint>,
    scalar_kind: Option<ScalarKind>,
}

fn pointer_rank(hint: PointerHint) -> u8 {
    match hint {
        PointerHint::Unknown => 0,
        PointerHint::PointerLike => 1,
        PointerHint::CodePointer => 2,
    }
}

fn scalar_rank(kind: ScalarKind) -> u8 {
    match kind {
        ScalarKind::Unknown => 0,
        ScalarKind::Bitvector => 1,
        ScalarKind::Bool | ScalarKind::SignedInt | ScalarKind::UnsignedInt | ScalarKind::Float => 2,
    }
}

fn storage_rank(class: StorageClass) -> u8 {
    match class {
        StorageClass::Unknown => 0,
        StorageClass::Register => 1,
        StorageClass::Stack
        | StorageClass::Heap
        | StorageClass::Global
        | StorageClass::ThreadLocal
        | StorageClass::ConstData
        | StorageClass::Volatile => 2,
    }
}

fn memory_class_rank(class: MemoryClass) -> u8 {
    match class {
        MemoryClass::Unknown => 0,
        MemoryClass::Ram => 1,
        MemoryClass::Stack
        | MemoryClass::Heap
        | MemoryClass::Global
        | MemoryClass::ThreadLocal
        | MemoryClass::Mmio
        | MemoryClass::IoPort
        | MemoryClass::Code => 2,
    }
}

fn merge_inferred_field<T: Copy>(
    slot: &mut Option<T>,
    incoming: Option<T>,
    rank: impl Fn(T) -> u8,
) {
    let Some(new_val) = incoming else {
        return;
    };
    match slot {
        Some(old_val) if rank(*old_val) >= rank(new_val) => {}
        _ => {
            *slot = Some(new_val);
        }
    }
}

fn merge_inferred_semantics(dst: &mut InferredSemantics, src: InferredSemantics) {
    merge_inferred_field(&mut dst.storage_class, src.storage_class, storage_rank);
    merge_inferred_field(&mut dst.pointer_hint, src.pointer_hint, pointer_rank);
    merge_inferred_field(&mut dst.scalar_kind, src.scalar_kind, scalar_rank);
}

fn varnode_existing_inference(vn: &Varnode) -> InferredSemantics {
    let Some(meta) = vn.meta.as_ref() else {
        return InferredSemantics::default();
    };

    InferredSemantics {
        storage_class: meta
            .storage_class
            .filter(|v| !matches!(v, StorageClass::Unknown)),
        pointer_hint: meta
            .pointer_hint
            .filter(|v| !matches!(v, PointerHint::Unknown)),
        scalar_kind: meta
            .scalar_kind
            .filter(|v| !matches!(v, ScalarKind::Unknown)),
    }
}

fn update_inferred_semantics(
    inferred: &mut HashMap<VnKey, InferredSemantics>,
    vn: &Varnode,
    incoming: InferredSemantics,
) {
    let entry = inferred.entry(VnKey::from(vn)).or_default();
    merge_inferred_semantics(entry, incoming);
}

fn merged_varnode_inference(
    inferred: &HashMap<VnKey, InferredSemantics>,
    vn: &Varnode,
) -> InferredSemantics {
    let mut out = varnode_existing_inference(vn);
    if let Some(cur) = inferred.get(&VnKey::from(vn)) {
        merge_inferred_semantics(&mut out, *cur);
    }
    out
}

fn is_x86_arch(arch_name: &str) -> bool {
    arch_name.contains("x86")
}

fn is_stack_register(arch_name: &str, reg: &str) -> bool {
    if is_x86_arch(arch_name) {
        matches!(reg, "rsp" | "esp" | "sp" | "rbp" | "ebp" | "bp")
    } else {
        matches!(
            reg,
            "sp" | "rsp" | "esp" | "bp" | "rbp" | "ebp" | "fp" | "s0" | "x2" | "x8"
        )
    }
}

/// Read `<programcounter register="..."/>` out of a Ghidra processor spec.
fn program_counter_from_pspec(pspec: &str) -> String {
    const KEY: &str = "programcounter";
    let Some(rest) = pspec.split_once(KEY).map(|(_, rest)| rest) else {
        return "pc".to_string();
    };
    let Some(rest) = rest.split_once("register=").map(|(_, rest)| rest) else {
        return "pc".to_string();
    };
    let rest = rest.trim_start();
    let quote = match rest.chars().next() {
        Some(c @ ('"' | '\'')) => c,
        _ => return "pc".to_string(),
    };
    rest[1..]
        .split(quote)
        .next()
        .filter(|name| !name.is_empty())
        .unwrap_or("pc")
        .to_string()
}

fn is_pc_register(reg: &str) -> bool {
    matches!(reg, "pc" | "rip" | "eip" | "ip")
}

fn is_x86_tls_register(arch_name: &str, reg: &str) -> bool {
    is_x86_arch(arch_name)
        && matches!(
            reg,
            "fs" | "gs" | "fsbase" | "gsbase" | "fs_base" | "gs_base"
        )
}

fn infer_address_storage_from_register(arch_name: &str, reg: &str) -> Option<StorageClass> {
    if is_x86_tls_register(arch_name, reg) {
        return Some(StorageClass::ThreadLocal);
    }
    if is_stack_register(arch_name, reg) {
        return Some(StorageClass::Stack);
    }
    if is_pc_register(reg) {
        return Some(StorageClass::Global);
    }
    None
}

fn map_storage_to_memory_class(storage: StorageClass) -> MemoryClass {
    match storage {
        StorageClass::Stack => MemoryClass::Stack,
        StorageClass::Heap => MemoryClass::Heap,
        StorageClass::Global => MemoryClass::Global,
        StorageClass::ThreadLocal => MemoryClass::ThreadLocal,
        StorageClass::Volatile => MemoryClass::Mmio,
        _ => MemoryClass::Ram,
    }
}

fn infer_op_memory_class(existing: Option<MemoryClass>, incoming: MemoryClass) -> MemoryClass {
    match existing {
        Some(cur) if memory_class_rank(cur) >= memory_class_rank(incoming) => cur,
        _ => incoming,
    }
}

fn infer_op_permissions(op: &R2ILOp, memory_class: MemoryClass) -> Option<MemoryPermissions> {
    let (read, write) = match op {
        R2ILOp::Load { .. } | R2ILOp::LoadLinked { .. } | R2ILOp::LoadGuarded { .. } => {
            (true, false)
        }
        R2ILOp::Store { .. } | R2ILOp::StoreConditional { .. } | R2ILOp::StoreGuarded { .. } => {
            (false, true)
        }
        R2ILOp::AtomicCAS { .. } => (true, true),
        _ => return None,
    };

    let (volatile, cacheable) = match memory_class {
        MemoryClass::Mmio | MemoryClass::IoPort => (true, false),
        _ => (false, true),
    };

    Some(MemoryPermissions {
        read,
        write,
        execute: matches!(memory_class, MemoryClass::Code),
        volatile,
        cacheable,
    })
}

fn apply_inferred_to_varnode(vn: &mut Varnode, inferred: &HashMap<VnKey, InferredSemantics>) {
    let Some(extra) = inferred.get(&VnKey::from(&*vn)).copied() else {
        return;
    };

    let mut meta = vn.meta.clone().unwrap_or_default();
    let mut changed = false;

    if let Some(storage) = extra.storage_class {
        match meta.storage_class {
            Some(cur) if storage_rank(cur) >= storage_rank(storage) => {}
            _ => {
                meta.storage_class = Some(storage);
                changed = true;
            }
        }
    }

    if let Some(hint) = extra.pointer_hint {
        match meta.pointer_hint {
            Some(cur) if pointer_rank(cur) >= pointer_rank(hint) => {}
            _ => {
                meta.pointer_hint = Some(hint);
                changed = true;
            }
        }
    }

    if let Some(kind) = extra.scalar_kind {
        match meta.scalar_kind {
            Some(cur) if scalar_rank(cur) >= scalar_rank(kind) => {}
            _ => {
                meta.scalar_kind = Some(kind);
                changed = true;
            }
        }
    }

    if changed {
        vn.meta = Some(meta);
    }
}

fn cached_register_name<F>(
    vn: &Varnode,
    reg_name_cache: &mut HashMap<VnKey, Option<String>>,
    resolve_register: &F,
) -> Option<String>
where
    F: Fn(&Varnode) -> Option<String>,
{
    if !vn.is_register() {
        return None;
    }

    let key = VnKey::from(vn);
    if let Some(cached) = reg_name_cache.get(&key) {
        return cached.clone();
    }

    let resolved = resolve_register(vn).map(|name| name.to_ascii_lowercase());
    reg_name_cache.insert(key, resolved.clone());
    resolved
}

fn inferred_address_storage<F>(
    vn: &Varnode,
    inferred: &HashMap<VnKey, InferredSemantics>,
    arch_name: &str,
    reg_name_cache: &mut HashMap<VnKey, Option<String>>,
    resolve_register: &F,
) -> Option<StorageClass>
where
    F: Fn(&Varnode) -> Option<String>,
{
    if let Some(info) = inferred.get(&VnKey::from(vn))
        && let Some(storage) = info.storage_class
        && !matches!(storage, StorageClass::Register | StorageClass::Unknown)
    {
        return Some(storage);
    }

    if let Some(name) = cached_register_name(vn, reg_name_cache, resolve_register) {
        return infer_address_storage_from_register(arch_name, &name);
    }

    None
}

fn annotate_semantic_metadata_with_hints<F>(
    block: &mut R2ILBlock,
    arch_name: &str,
    options: SemanticMetadataOptions,
    resolve_register: F,
) where
    F: Fn(&Varnode) -> Option<String>,
{
    if !options.enabled {
        return;
    }
    if !matches!(options.precision, SemanticMetadataPrecision::High) {
        return;
    }

    let arch = arch_name.to_ascii_lowercase();
    let mut inferred: HashMap<VnKey, InferredSemantics> = HashMap::new();
    let mut reg_name_cache: HashMap<VnKey, Option<String>> = HashMap::new();
    let mut op_memory_updates: Vec<(usize, MemoryClass, MemoryPermissions)> = Vec::new();

    for op in &block.ops {
        if let Some(dst) = op.output()
            && dst.is_register()
        {
            update_inferred_semantics(
                &mut inferred,
                dst,
                InferredSemantics {
                    storage_class: Some(StorageClass::Register),
                    ..Default::default()
                },
            );
        }
        for src in op.inputs() {
            if src.is_register() {
                update_inferred_semantics(
                    &mut inferred,
                    src,
                    InferredSemantics {
                        storage_class: Some(StorageClass::Register),
                        ..Default::default()
                    },
                );
            }
        }
    }

    for (op_index, op) in block.ops.iter().enumerate() {
        let mut dst_infer = InferredSemantics::default();
        match op {
            R2ILOp::Load { addr, .. }
            | R2ILOp::LoadLinked { addr, .. }
            | R2ILOp::LoadGuarded { addr, .. }
            | R2ILOp::Store { addr, .. }
            | R2ILOp::StoreConditional { addr, .. }
            | R2ILOp::StoreGuarded { addr, .. }
            | R2ILOp::AtomicCAS { addr, .. } => {
                update_inferred_semantics(
                    &mut inferred,
                    addr,
                    InferredSemantics {
                        pointer_hint: Some(PointerHint::PointerLike),
                        ..Default::default()
                    },
                );
                let addr_storage = inferred_address_storage(
                    addr,
                    &inferred,
                    &arch,
                    &mut reg_name_cache,
                    &resolve_register,
                );
                if let Some(storage) = addr_storage {
                    update_inferred_semantics(
                        &mut inferred,
                        addr,
                        InferredSemantics {
                            storage_class: Some(storage),
                            ..Default::default()
                        },
                    );
                }
                let memory_class =
                    map_storage_to_memory_class(addr_storage.unwrap_or(StorageClass::Unknown));
                if let Some(permissions) = infer_op_permissions(op, memory_class) {
                    op_memory_updates.push((op_index, memory_class, permissions));
                }
            }
            R2ILOp::CallInd { target } | R2ILOp::BranchInd { target } => {
                update_inferred_semantics(
                    &mut inferred,
                    target,
                    InferredSemantics {
                        pointer_hint: Some(PointerHint::CodePointer),
                        ..Default::default()
                    },
                );
            }
            R2ILOp::PtrAdd { base, .. } | R2ILOp::PtrSub { base, .. } => {
                dst_infer.pointer_hint = Some(PointerHint::PointerLike);
                dst_infer.storage_class = inferred_address_storage(
                    base,
                    &inferred,
                    &arch,
                    &mut reg_name_cache,
                    &resolve_register,
                );
            }
            R2ILOp::SegmentOp {
                segment, offset, ..
            } => {
                dst_infer.pointer_hint = Some(PointerHint::PointerLike);
                let seg_storage = inferred_address_storage(
                    segment,
                    &inferred,
                    &arch,
                    &mut reg_name_cache,
                    &resolve_register,
                );
                let off_storage = inferred_address_storage(
                    offset,
                    &inferred,
                    &arch,
                    &mut reg_name_cache,
                    &resolve_register,
                );
                dst_infer.storage_class = seg_storage.or(off_storage);
            }
            R2ILOp::Copy { src, .. } | R2ILOp::Cast { src, .. } | R2ILOp::New { src, .. } => {
                dst_infer = merged_varnode_inference(&inferred, src);
                if matches!(
                    dst_infer.storage_class,
                    None | Some(StorageClass::Unknown) | Some(StorageClass::Register)
                ) {
                    dst_infer.storage_class = inferred_address_storage(
                        src,
                        &inferred,
                        &arch,
                        &mut reg_name_cache,
                        &resolve_register,
                    )
                    .or(dst_infer.storage_class);
                }
            }
            R2ILOp::IntAdd { a, b, .. } | R2ILOp::IntSub { a, b, .. } => {
                let a_inf = merged_varnode_inference(&inferred, a);
                let b_inf = merged_varnode_inference(&inferred, b);
                let a_addr_storage = inferred_address_storage(
                    a,
                    &inferred,
                    &arch,
                    &mut reg_name_cache,
                    &resolve_register,
                );
                let b_addr_storage = inferred_address_storage(
                    b,
                    &inferred,
                    &arch,
                    &mut reg_name_cache,
                    &resolve_register,
                );
                let a_is_pointer = a_inf.pointer_hint.is_some() || a_addr_storage.is_some();
                let b_is_pointer = b_inf.pointer_hint.is_some() || b_addr_storage.is_some();
                if (a_is_pointer && b.is_const()) || (b_is_pointer && a.is_const()) {
                    dst_infer.pointer_hint = Some(PointerHint::PointerLike);
                    dst_infer.storage_class = if a_is_pointer {
                        a_addr_storage.or(a_inf.storage_class)
                    } else {
                        b_addr_storage.or(b_inf.storage_class)
                    };
                }
            }
            R2ILOp::BoolNot { .. }
            | R2ILOp::BoolAnd { .. }
            | R2ILOp::BoolOr { .. }
            | R2ILOp::BoolXor { .. }
            | R2ILOp::IntEqual { .. }
            | R2ILOp::IntNotEqual { .. }
            | R2ILOp::IntLess { .. }
            | R2ILOp::IntSLess { .. }
            | R2ILOp::IntLessEqual { .. }
            | R2ILOp::IntSLessEqual { .. }
            | R2ILOp::FloatEqual { .. }
            | R2ILOp::FloatNotEqual { .. }
            | R2ILOp::FloatLess { .. }
            | R2ILOp::FloatLessEqual { .. }
            | R2ILOp::FloatNaN { .. } => {
                dst_infer.scalar_kind = Some(ScalarKind::Bool);
            }
            R2ILOp::FloatAdd { .. }
            | R2ILOp::FloatSub { .. }
            | R2ILOp::FloatMult { .. }
            | R2ILOp::FloatDiv { .. }
            | R2ILOp::FloatNeg { .. }
            | R2ILOp::FloatAbs { .. }
            | R2ILOp::FloatSqrt { .. }
            | R2ILOp::FloatCeil { .. }
            | R2ILOp::FloatFloor { .. }
            | R2ILOp::FloatRound { .. }
            | R2ILOp::Int2Float { .. }
            | R2ILOp::FloatFloat { .. } => {
                dst_infer.scalar_kind = Some(ScalarKind::Float);
            }
            R2ILOp::IntSDiv { .. }
            | R2ILOp::IntSRem { .. }
            | R2ILOp::IntSRight { .. }
            | R2ILOp::IntSExt { .. }
            | R2ILOp::IntNegate { .. } => {
                dst_infer.scalar_kind = Some(ScalarKind::SignedInt);
            }
            R2ILOp::IntDiv { .. } | R2ILOp::IntRem { .. } | R2ILOp::IntZExt { .. } => {
                dst_infer.scalar_kind = Some(ScalarKind::UnsignedInt);
            }
            _ => {}
        }

        if let Some(dst) = op.output() {
            update_inferred_semantics(&mut inferred, dst, dst_infer);
        }
    }

    for (op_index, incoming_class, incoming_perms) in op_memory_updates {
        let current = block.op_metadata(op_index).and_then(|m| m.memory_class);
        let merged_class = infer_op_memory_class(current, incoming_class);
        let mut meta = block.op_metadata(op_index).cloned().unwrap_or_default();
        meta.memory_class = Some(merged_class);
        if meta.permissions.is_none() {
            meta.permissions = Some(incoming_perms);
        }
        block.set_op_metadata(op_index, meta);
    }

    for op in &mut block.ops {
        if let Some(dst) = op.output_mut() {
            apply_inferred_to_varnode(dst, &inferred);
        }
        for src in op.inputs_mut() {
            apply_inferred_to_varnode(src, &inferred);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::OpMetadata;

    const PINNED_ARM64_O2_LOAD_BLOCK_ADDR: u64 = 0x1_0000_05b4;
    const PINNED_ARM64_O2_LOAD_BLOCK: &[u8] = &[
        0x0a, 0x15, 0x40, 0x38, 0x4b, 0x05, 0x01, 0x51, 0x4c, 0x01, 0x1b, 0x32, 0x7f, 0x69, 0x00,
        0x71, 0x8a, 0x31, 0x8a, 0x1a, 0x0a, 0x00, 0x0a, 0xca, 0x40, 0x7d, 0x09, 0x9b, 0x21, 0x04,
        0x00, 0xf1, 0x01, 0xff, 0xff, 0x54,
    ];
    const PINNED_X86_CONDITIONAL_RETURN_ADDR: u64 = 0x1_0000_0650;
    const PINNED_X86_CONDITIONAL_RETURN_BYTES: &[u8] = &[
        0x55, 0x48, 0x89, 0xe5, 0x31, 0xc0, 0x81, 0xff, 0xad, 0xde, 0x00, 0x00, 0x0f, 0x94, 0xc0,
        0x5d, 0xc3,
    ];

    fn reg(offset: u64, size: u32) -> Varnode {
        Varnode::register(offset, size)
    }

    fn declared_register_storage(arch: &r2il::ArchSpec, name: &str) -> r2il::RegisterStorage {
        arch.get_register(name)
            .unwrap_or_else(|| panic!("embedded specification is missing {name}"))
            .storage()
    }

    fn register_varnode(storage: r2il::RegisterStorage) -> Varnode {
        Varnode::register(storage.offset, storage.size)
    }

    fn padded_instruction<const N: usize>(instruction: [u8; N]) -> [u8; 16] {
        let mut bytes = [0_u8; 16];
        bytes[..N].copy_from_slice(&instruction);
        bytes
    }

    #[cfg(feature = "x86")]
    #[test]
    fn x86_32_bit_register_write_explicitly_zero_extends_its_declared_carrier() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 specification");
        let bytes = padded_instruction([0x89, 0xd8]);
        let lifted = disassembler
            .lift_genuine_block(&bytes, 0x1000, 2)
            .expect("mov eax, ebx lift");
        let arch = lifted.authority().arch_spec();
        let eax = declared_register_storage(arch, "EAX");
        let ebx = declared_register_storage(arch, "EBX");
        let rax = declared_register_storage(arch, "RAX");

        assert_eq!(
            lifted.block().ops,
            vec![
                R2ILOp::Copy {
                    dst: register_varnode(eax),
                    src: register_varnode(ebx),
                },
                R2ILOp::IntZExt {
                    dst: register_varnode(rax),
                    src: register_varnode(eax),
                },
            ]
        );
    }

    #[cfg(feature = "arm")]
    #[test]
    fn aarch64_w_register_write_explicitly_zero_extends_its_declared_carrier() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::Aarch64Le)
            .expect("trusted AArch64 specification");
        // mov w0, w1 (alias of orr w0, wzr, w1), little-endian encoding.
        let bytes = padded_instruction([0xe0, 0x03, 0x01, 0x2a]);
        let lifted = disassembler
            .lift_genuine_block(&bytes, 0x1000, 4)
            .expect("mov w0, w1 lift");
        let arch = lifted.authority().arch_spec();
        let w0 = declared_register_storage(arch, "w0");
        let w1 = declared_register_storage(arch, "w1");
        let x0 = declared_register_storage(arch, "x0");

        assert_eq!(
            lifted.block().ops,
            vec![R2ILOp::IntZExt {
                dst: register_varnode(x0),
                src: register_varnode(w1),
            }]
        );
        assert!(matches!(
            arch.register_projection(w0).map(|projection| projection.disposition),
            Some(r2il::RegisterProjectionDisposition::Bound { carrier, .. })
                if carrier == x0
        ));
    }

    #[cfg(feature = "x86")]
    #[test]
    fn x86_imul_overflow_chain_retains_its_exact_128_bit_product_geometry() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 specification");
        let bytes = padded_instruction([0x4c, 0x0f, 0xaf, 0xca]);
        let lifted = disassembler
            .lift_genuine_block(&bytes, 0x1000, 4)
            .expect("imul r9, rdx genuine lift");
        let arch = lifted.authority().arch_spec();

        r2il::validate_block_semantic(lifted.block(), arch)
            .expect("genuine IMUL P-code is width coherent");
        let product = lifted.block().ops.iter().find_map(|op| match op {
            R2ILOp::IntMult { dst, a, b } if dst.size == 16 && a.size == 16 && b.size == 16 => {
                Some(dst)
            }
            _ => None,
        });
        let product = product.expect("exact signed 128-bit product");
        assert!(lifted.block().ops.iter().any(|op| matches!(
            op,
            R2ILOp::IntSExt { dst, src } if dst.size == 16 && src.size == 8
        )));
        assert!(lifted.block().ops.iter().any(|op| matches!(
            op,
            R2ILOp::IntNotEqual { a, b, .. }
                if a.size == 16 && b == product
        )));
    }

    #[cfg(feature = "arm")]
    #[test]
    fn aarch64_dup_and_sbfx_retain_proven_width_changes() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::Aarch64Le)
            .expect("trusted AArch64 specification");

        let dup = disassembler
            .lift_genuine_block(&padded_instruction([0x40, 0x0c, 0x04, 0x4e]), 0x1000, 4)
            .expect("dup v0.4s, w2 genuine lift");
        r2il::validate_block_semantic(dup.block(), dup.authority().arch_spec())
            .expect("genuine DUP P-code is width coherent");
        assert!(dup.block().ops.iter().all(|op| match op {
            R2ILOp::Copy { dst, src } => dst.size == src.size,
            _ => true,
        }));

        let sbfx = disassembler
            .lift_genuine_block(&padded_instruction([0x4b, 0x01, 0x00, 0x13]), 0x2000, 4)
            .expect("sbfx w11, w10, 0, 1 genuine lift");
        r2il::validate_block_semantic(sbfx.block(), sbfx.authority().arch_spec())
            .expect("genuine SBFX P-code is width coherent");
        assert!(sbfx.block().ops.iter().any(|op| matches!(
            op,
            R2ILOp::IntZExt { dst, src } if dst.size == 8 && src.size == 4
        )));
    }

    #[cfg(feature = "x86")]
    #[test]
    fn x86_byte_register_writes_do_not_invent_full_carrier_zero_extensions() {
        for (instruction, destination_name) in [([0x88, 0xd8], "AL"), ([0x88, 0xdc], "AH")] {
            let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
                .expect("trusted x86-64 specification");
            let bytes = padded_instruction(instruction);
            let lifted = disassembler
                .lift_genuine_block(&bytes, 0x1000, 2)
                .unwrap_or_else(|error| panic!("mov {destination_name}, bl lift: {error}"));
            let arch = lifted.authority().arch_spec();
            let destination = declared_register_storage(arch, destination_name);
            let bl = declared_register_storage(arch, "BL");
            let rax = declared_register_storage(arch, "RAX");

            assert_eq!(
                lifted.block().ops,
                vec![R2ILOp::Copy {
                    dst: register_varnode(destination),
                    src: register_varnode(bl),
                }]
            );
            assert!(!lifted.block().ops.iter().any(|op| matches!(
                op,
                R2ILOp::IntZExt { dst, src }
                    if dst == &register_varnode(rax)
                        && src == &register_varnode(destination)
            )));
        }
    }

    #[test]
    fn pinned_arm64_memory_space_is_ram_and_instance_stable() {
        let first = Disassembler::from_sla(
            sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
            sleigh_config::processor_aarch64::PSPEC_AARCH64,
            "aarch64",
        )
        .expect("first AARCH64 AppleSilicon disassembler");
        let second = Disassembler::from_sla(
            sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
            sleigh_config::processor_aarch64::PSPEC_AARCH64,
            "aarch64",
        )
        .expect("second AARCH64 AppleSilicon disassembler");

        let first_block = first
            .lift_block(
                PINNED_ARM64_O2_LOAD_BLOCK,
                PINNED_ARM64_O2_LOAD_BLOCK_ADDR,
                PINNED_ARM64_O2_LOAD_BLOCK.len(),
            )
            .expect("first real ARM64 O2 FNV lift");
        let second_block = second
            .lift_block(
                PINNED_ARM64_O2_LOAD_BLOCK,
                PINNED_ARM64_O2_LOAD_BLOCK_ADDR,
                PINNED_ARM64_O2_LOAD_BLOCK.len(),
            )
            .expect("second real ARM64 O2 FNV lift");

        for block in [&first_block, &second_block] {
            let memory_spaces = block
                .ops
                .iter()
                .filter_map(|op| match op {
                    R2ILOp::Load { space, .. } | R2ILOp::Store { space, .. } => Some(*space),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert!(
                !memory_spaces.is_empty(),
                "real block must contain memory IO"
            );
            assert!(
                memory_spaces.iter().all(|space| *space == SpaceId::Ram),
                "real ARM64 LOAD/STORE spaces must translate to Ram: {memory_spaces:?}"
            );
        }

        assert_eq!(first_block.addr, second_block.addr);
        assert_eq!(first_block.size as usize, PINNED_ARM64_O2_LOAD_BLOCK.len());
        assert_eq!(second_block.size as usize, PINNED_ARM64_O2_LOAD_BLOCK.len());
        assert_eq!(first_block.size, second_block.size);
        assert_eq!(first_block.ops, second_block.ops);
        assert_eq!(first_block.op_metadata, second_block.op_metadata);
        assert!(first_block.switch_info.is_none());
        assert!(second_block.switch_info.is_none());
    }

    #[test]
    #[cfg(feature = "arm")]
    fn trusted_arm64_radare_tuple_selects_generic_aarch64() {
        assert_eq!(
            TrustedSleighProfile::from_tuple("arm", "arm", 64, SourceEndianness::Little)
                .expect("verified radare ARM64 tuple"),
            TrustedSleighProfile::Aarch64Le
        );
    }

    #[test]
    #[cfg(feature = "arm")]
    fn trusted_arm64_radare_tuple_refuses_unverified_neighbors() {
        for (arch_id, cpu_id, bits, endianness) in [
            ("arm", "arm", 32, SourceEndianness::Little),
            ("arm", "arm", 64, SourceEndianness::Big),
            ("aarch64", "arm", 64, SourceEndianness::Little),
            ("arm", "arm64", 64, SourceEndianness::Little),
            ("arm", "all", 64, SourceEndianness::Little),
        ] {
            assert!(matches!(
                TrustedSleighProfile::from_tuple(arch_id, cpu_id, bits, endianness),
                Err(LiftError::Unsupported(_))
            ));
        }
    }

    #[test]
    #[cfg(not(feature = "arm"))]
    fn trusted_arm64_radare_tuple_requires_arm_feature() {
        assert!(matches!(
            TrustedSleighProfile::from_tuple("arm", "arm", 64, SourceEndianness::Little),
            Err(LiftError::Unsupported(_))
        ));
    }

    #[test]
    #[cfg(feature = "arm")]
    fn trusted_generic_aarch64_profile_lifts_pinned_real_bytes() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::Aarch64Le)
            .expect("trusted generic AArch64 disassembler");
        let block = disassembler
            .lift_genuine_block(
                PINNED_ARM64_O2_LOAD_BLOCK,
                PINNED_ARM64_O2_LOAD_BLOCK_ADDR,
                PINNED_ARM64_O2_LOAD_BLOCK.len(),
            )
            .expect("genuine lift of pinned real ARM64 bytes");

        assert_eq!(block.source_bytes(), PINNED_ARM64_O2_LOAD_BLOCK);
        assert_eq!(block.block().addr, PINNED_ARM64_O2_LOAD_BLOCK_ADDR);
        assert_eq!(
            block.block().size as usize,
            PINNED_ARM64_O2_LOAD_BLOCK.len()
        );
        assert_eq!(block.authority().arch_name(), "aarch64");
        assert!(!block.block().ops.is_empty());
    }

    #[test]
    fn genuine_lift_binds_full_bytes_to_one_opaque_session() {
        let first = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("first trusted x86-64 disassembler");
        let second = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("independent trusted x86-64 disassembler");

        let mut first_bytes = PINNED_X86_CONDITIONAL_RETURN_BYTES.to_vec();
        let first_entry = first
            .lift_genuine_block(
                &first_bytes,
                PINNED_X86_CONDITIONAL_RETURN_ADDR,
                first_bytes.len(),
            )
            .expect("complete genuine entry lift");
        first_bytes.fill(0);
        assert_eq!(
            first_entry.source_bytes(),
            PINNED_X86_CONDITIONAL_RETURN_BYTES
        );
        let first_blocks = vec![first_entry];
        let layout = GenuineFunctionLayout::new(
            b"pinned-check-secret-o2-complete-function".to_vec(),
            PINNED_X86_CONDITIONAL_RETURN_ADDR,
            [GenuineFunctionBlockRange::new(
                PINNED_X86_CONDITIONAL_RETURN_ADDR,
                u32::try_from(PINNED_X86_CONDITIONAL_RETURN_BYTES.len()).expect("block size"),
            )],
            [],
        )
        .expect("exact complete function layout");
        let function = GenuineLiftedFunction::try_from_layout(layout.clone(), first_blocks.clone())
            .expect("closed single-session genuine function");
        let function_alias = function.clone();
        assert!(
            function.authority().same_lift(function_alias.authority()),
            "clones must preserve the same opaque function-lift identity"
        );
        assert!(
            function
                .authority()
                .lift_authority()
                .same_session(first_blocks[0].authority())
        );
        assert_eq!(function.blocks().len(), 1);
        let pinned_block = &function.blocks()[0];
        assert_eq!(
            pinned_block
                .instruction_spans()
                .iter()
                .map(|span| (span.addr(), span.size()))
                .collect::<Vec<_>>(),
            vec![
                (PINNED_X86_CONDITIONAL_RETURN_ADDR, 1),
                (PINNED_X86_CONDITIONAL_RETURN_ADDR + 1, 3),
                (PINNED_X86_CONDITIONAL_RETURN_ADDR + 4, 2),
                (PINNED_X86_CONDITIONAL_RETURN_ADDR + 6, 6),
                (PINNED_X86_CONDITIONAL_RETURN_ADDR + 12, 3),
                (PINNED_X86_CONDITIONAL_RETURN_ADDR + 15, 1),
                (PINNED_X86_CONDITIONAL_RETURN_ADDR + 16, 1),
            ],
            "native instruction coverage must match the manually reversed function"
        );
        let memory_spaces = pinned_block
            .block()
            .ops
            .iter()
            .filter_map(|op| match op {
                R2ILOp::Load { space, .. } | R2ILOp::Store { space, .. } => Some(*space),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(memory_spaces, vec![SpaceId::Ram; 3]);
        assert!(pinned_block.block().ops.iter().any(|op| matches!(
            op,
            R2ILOp::Copy { dst, src }
                if dst.space == SpaceId::Unique
                    && dst.size == 4
                    && src == &Varnode::register(56, 4)
        )));
        assert!(pinned_block.block().ops.iter().any(|op| matches!(
            op,
            R2ILOp::IntSub { b, .. }
                if b.space == SpaceId::Const && b.offset == 0xdead && b.size == 4
        )));
        assert!(pinned_block.block().ops.iter().any(|op| matches!(
            op,
            R2ILOp::Copy { dst, src }
                if dst == &Varnode::register(0, 1)
                    && src == &Varnode::register(518, 1)
        )));
        assert!(matches!(
            pinned_block.block().ops.last(),
            Some(R2ILOp::Return { target }) if target == &Varnode::register(648, 8)
        ));
        for metadata in function.blocks()[0].block().op_metadata.values() {
            let mut canonical = metadata.clone();
            assert!(canonical.instruction_addr.is_some());
            canonical.instruction_addr = None;
            assert_eq!(
                canonical,
                OpMetadata::default(),
                "certifying lift must not retain inferred semantic metadata"
            );
        }

        let second_blocks = vec![
            second
                .lift_genuine_block(
                    PINNED_X86_CONDITIONAL_RETURN_BYTES,
                    PINNED_X86_CONDITIONAL_RETURN_ADDR,
                    PINNED_X86_CONDITIONAL_RETURN_BYTES.len(),
                )
                .expect("independent genuine function block"),
        ];
        assert!(
            !first_blocks[0]
                .authority()
                .same_session(second_blocks[0].authority())
        );
        assert!(
            GenuineLiftedFunction::try_from_layout(layout.clone(), Vec::new()).is_err(),
            "omitting a declared genuine block must fail closed"
        );
        let independent = GenuineLiftedFunction::try_from_layout(layout, second_blocks)
            .expect("an independently complete session is genuine in its own right");
        assert_eq!(
            function.authority().source_manifest_hash(),
            independent.authority().source_manifest_hash(),
            "identical immutable inputs should retain the same diagnostic manifest"
        );
        assert!(
            !function.authority().same_lift(independent.authority()),
            "a matching diagnostic manifest must not replay function-lift authority"
        );
        let authorities = HashSet::from([
            function.authority().clone(),
            independent.authority().clone(),
        ]);
        assert_eq!(
            authorities.len(),
            2,
            "authority hashing must use opaque event identity"
        );
    }

    #[test]
    fn genuine_zero_op_instructions_preserve_exact_native_spans_without_changing_pcode() {
        const ADDR: u64 = 0x401000;
        const BYTES: &[u8] = &[0x90, 0x31, 0xc0, 0x90];

        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 disassembler");
        let lifted = disassembler
            .lift_genuine_block(BYTES, ADDR, BYTES.len())
            .expect("genuine NOP/XOR/NOP block");
        let canonical_ops = lifted.block().ops.clone();
        let canonical_metadata = lifted.block().op_metadata.clone();
        let spans = lifted
            .instruction_spans()
            .iter()
            .map(|span| {
                (
                    span.addr(),
                    span.size(),
                    span.first_canonical_op(),
                    span.canonical_op_count(),
                )
            })
            .collect::<Vec<_>>();

        let xor_op_count = u64::try_from(canonical_ops.len()).expect("canonical op count fits u64");
        assert_eq!(
            spans,
            vec![
                (ADDR, 1, 0, 0),
                (ADDR + 1, 2, 0, xor_op_count),
                (ADDR + 3, 1, xor_op_count, 0),
            ]
        );
        assert!(
            !canonical_ops.is_empty(),
            "XOR must retain canonical P-code"
        );
        assert!(
            !canonical_ops
                .iter()
                .any(|op| matches!(op, R2ILOp::Unimplemented))
        );
        assert!(
            canonical_metadata
                .values()
                .all(|metadata| metadata.instruction_addr == Some(ADDR + 1))
        );

        assert_eq!(lifted.source_bytes(), BYTES);
        assert_eq!(lifted.block().ops, canonical_ops);
        assert_eq!(lifted.block().op_metadata, canonical_metadata);
    }

    #[test]
    fn genuine_consecutive_all_zero_op_spans_remain_first_class_native_evidence() {
        const ADDR: u64 = 0x402000;
        const BYTES: &[u8] = &[0x90, 0x90, 0x90];

        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 disassembler");
        let lifted = disassembler
            .lift_genuine_block(BYTES, ADDR, BYTES.len())
            .expect("genuine consecutive NOP block");

        assert!(lifted.block().ops.is_empty());
        assert!(lifted.block().op_metadata.is_empty());
        assert_eq!(lifted.source_bytes(), BYTES);
        assert_eq!(
            lifted
                .instruction_spans()
                .iter()
                .map(|span| {
                    (
                        span.addr(),
                        span.size(),
                        span.first_canonical_op(),
                        span.canonical_op_count(),
                    )
                })
                .collect::<Vec<_>>(),
            vec![(ADDR, 1, 0, 0), (ADDR + 1, 1, 0, 0), (ADDR + 2, 1, 0, 0),]
        );
    }

    #[cfg(any(feature = "arm", feature = "riscv"))]
    fn assert_public_lifts_preserve_canonical_ops(
        disassembler: &Disassembler,
        bytes: &[u8],
        addr: u64,
    ) -> R2ILBlock {
        let mut padded = bytes.to_vec();
        padded.resize(Disassembler::MIN_BYTES, 0);
        let canonical = disassembler
            .lift_canonical(&padded, addr)
            .expect("canonical Sleigh lift");
        let default = disassembler
            .lift(&padded, addr)
            .expect("default public lift");
        let disabled = disassembler
            .lift_with_options(
                &padded,
                addr,
                SemanticMetadataOptions {
                    enabled: false,
                    ..Default::default()
                },
            )
            .expect("public lift without advisory metadata");

        assert_eq!(default.ops, canonical.ops);
        assert_eq!(disabled.ops, canonical.ops);
        canonical
    }

    #[cfg(any(feature = "arm", feature = "riscv"))]
    fn assert_native_instruction(
        disassembler: &Disassembler,
        bytes: &[u8],
        addr: u64,
        expected_token: &str,
    ) {
        let mut padded = bytes.to_vec();
        padded.resize(Disassembler::MIN_BYTES, 0);
        let (instruction, size) = disassembler
            .disasm_native(&padded, addr)
            .expect("native instruction decode");
        assert_eq!(size, bytes.len());
        assert_eq!(
            instruction
                .split_whitespace()
                .next()
                .unwrap_or_default()
                .to_ascii_lowercase(),
            expected_token
        );
    }

    #[cfg(feature = "arm")]
    #[test]
    fn aarch64_pauth_and_barrier_retain_only_canonical_sleigh_semantics() {
        const PACIBSP: &[u8] = &[0x7f, 0x23, 0x03, 0xd5];
        const DMB_ISH: &[u8] = &[0xbf, 0x3b, 0x03, 0xd5];
        const ADDR: u64 = 0x410000;

        let disassembler =
            Disassembler::from_trusted_profile(TrustedSleighProfile::Aarch64AppleSilicon)
                .expect("trusted Apple AArch64 disassembler");
        assert_native_instruction(&disassembler, PACIBSP, ADDR, "pacibsp");
        assert_native_instruction(&disassembler, DMB_ISH, ADDR + PACIBSP.len() as u64, "dmb");
        let pacibsp = assert_public_lifts_preserve_canonical_ops(&disassembler, PACIBSP, ADDR);
        assert!(
            pacibsp.ops.is_empty(),
            "zero-P-code PACIBSP must not acquire fabricated CallOther semantics"
        );

        let genuine = disassembler
            .lift_genuine_block(PACIBSP, ADDR, PACIBSP.len())
            .expect("genuine PACIBSP lift");
        assert!(genuine.block().ops.is_empty());
        assert_eq!(genuine.source_bytes(), PACIBSP);
        assert_eq!(
            genuine
                .instruction_spans()
                .iter()
                .map(|span| {
                    (
                        span.addr(),
                        span.size(),
                        span.first_canonical_op(),
                        span.canonical_op_count(),
                    )
                })
                .collect::<Vec<_>>(),
            vec![(ADDR, 4, 0, 0)]
        );

        let barrier = assert_public_lifts_preserve_canonical_ops(
            &disassembler,
            DMB_ISH,
            ADDR + PACIBSP.len() as u64,
        );
        let numeric_userops = barrier
            .ops
            .iter()
            .filter_map(|op| match op {
                R2ILOp::CallOther { userop, .. } => Some(*userop),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(
            !numeric_userops.is_empty(),
            "DMB must retain the translator's numeric CallOther evidence"
        );
        assert!(
            !barrier
                .ops
                .iter()
                .any(|op| matches!(op, R2ILOp::Fence { .. }))
        );

        let independent =
            Disassembler::from_trusted_profile(TrustedSleighProfile::Aarch64AppleSilicon)
                .expect("independent trusted Apple AArch64 disassembler");
        let repeated = assert_public_lifts_preserve_canonical_ops(
            &independent,
            DMB_ISH,
            ADDR + PACIBSP.len() as u64,
        );
        assert_eq!(repeated.ops, barrier.ops);
    }

    #[cfg(feature = "riscv")]
    #[test]
    fn riscv_atomic_bytes_retain_only_canonical_sleigh_semantics() {
        const FENCE_IORW_IORW: &[u8] = &[0x0f, 0x00, 0xf0, 0x0f];
        const LR_W_A0_A1: &[u8] = &[0x2f, 0xa5, 0x05, 0x10];
        const SC_W_A0_A1_A2: &[u8] = &[0x2f, 0x25, 0xb6, 0x18];
        const AMOADD_W_AQRL_A0_A1_A2: &[u8] = &[0x2f, 0x25, 0xb6, 0x06];
        const ADDR: u64 = 0x420000;

        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::RiscV64Gc)
            .expect("trusted RV64GC disassembler");
        for (index, (bytes, expected_token)) in [
            (FENCE_IORW_IORW, "fence"),
            (LR_W_A0_A1, "lr.w"),
            (SC_W_A0_A1_A2, "sc.w"),
            (AMOADD_W_AQRL_A0_A1_A2, "amoadd.w.aqrl"),
        ]
        .into_iter()
        .enumerate()
        {
            assert_native_instruction(
                &disassembler,
                bytes,
                ADDR + (index as u64 * 4),
                expected_token,
            );
            let canonical = assert_public_lifts_preserve_canonical_ops(
                &disassembler,
                bytes,
                ADDR + (index as u64 * 4),
            );
            assert!(
                !canonical.ops.iter().any(|op| matches!(
                    op,
                    R2ILOp::Fence { .. }
                        | R2ILOp::LoadLinked { .. }
                        | R2ILOp::StoreConditional { .. }
                )),
                "mnemonic-derived atomic operations must not be synthesized"
            );
        }
    }

    #[test]
    fn genuine_instruction_span_address_overflow_fails_closed() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 disassembler");

        assert!(
            disassembler
                .lift_genuine_block(&[0x90, 0x90], u64::MAX, 2)
                .is_err()
        );
    }

    #[test]
    fn genuine_lift_rejects_partial_or_empty_source_ranges() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 disassembler");

        assert!(
            disassembler
                .lift_genuine_block(
                    PINNED_X86_CONDITIONAL_RETURN_BYTES,
                    PINNED_X86_CONDITIONAL_RETURN_ADDR,
                    0,
                )
                .is_err()
        );
        assert!(
            disassembler
                .lift_genuine_block(
                    PINNED_X86_CONDITIONAL_RETURN_BYTES,
                    PINNED_X86_CONDITIONAL_RETURN_ADDR,
                    PINNED_X86_CONDITIONAL_RETURN_BYTES.len() + 1,
                )
                .is_err()
        );
    }

    #[test]
    fn arbitrary_specs_cannot_mint_genuine_lifts() {
        let arbitrary = Disassembler::from_sla(
            sleigh_config::processor_x86::SLA_X86_64,
            sleigh_config::processor_x86::PSPEC_X86_64,
            "x86-64",
        )
        .expect("analysis-only disassembler");
        assert!(
            arbitrary
                .lift_genuine_block(
                    PINNED_X86_CONDITIONAL_RETURN_BYTES,
                    PINNED_X86_CONDITIONAL_RETURN_ADDR,
                    PINNED_X86_CONDITIONAL_RETURN_BYTES.len(),
                )
                .is_err(),
            "even byte-identical caller-supplied specs remain analysis-only"
        );
    }

    #[test]
    fn fixed_value_pcode_uses_the_typed_sleigh_translation() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 disassembler");
        let address_spaces = disassembler.address_spaces();
        let constant_space = address_spaces
            .iter()
            .find(|space| space.space_type == libsla::AddressSpaceType::Constant)
            .expect("constant space")
            .clone();
        let register_space = address_spaces
            .iter()
            .find(|space| space.name == "register")
            .expect("register space")
            .clone();
        let address = Address::new(
            disassembler.default_code_space(),
            PINNED_X86_CONDITIONAL_RETURN_ADDR,
        );
        let copy = PcodeInstruction {
            address: address.clone(),
            op_code: OpCode::Copy,
            inputs: vec![VarnodeData::new(
                Address::new(constant_space.clone(), 42),
                8,
            )],
            output: Some(VarnodeData::new(Address::new(register_space.clone(), 0), 8)),
        };
        let add = PcodeInstruction {
            address,
            op_code: OpCode::Int(IntOp::Add),
            inputs: vec![
                VarnodeData::new(Address::new(register_space.clone(), 0), 4),
                VarnodeData::new(Address::new(constant_space, 1), 4),
            ],
            output: Some(VarnodeData::new(Address::new(register_space, 0), 4)),
        };

        assert_eq!(
            disassembler
                .translate_pcode_op(&copy)
                .expect("COPY translation"),
            Some(R2ILOp::Copy {
                dst: Varnode::register(0, 8),
                src: Varnode::constant(42, 8),
            })
        );
        assert_eq!(
            disassembler
                .translate_pcode_op(&add)
                .expect("INT_ADD translation"),
            Some(R2ILOp::IntAdd {
                dst: Varnode::register(0, 4),
                a: Varnode::register(0, 4),
                b: Varnode::constant(1, 4),
            })
        );
    }

    #[test]
    fn fixed_ram_copy_is_canonical_memory_io() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 disassembler");
        let ram_space = disassembler.default_code_space();
        let register_space = disassembler
            .address_spaces()
            .into_iter()
            .find(|space| space.name == "register")
            .expect("register space");
        let address_size = u32::try_from(ram_space.address_size).expect("r2il address size");
        let address = Address::new(ram_space.clone(), PINNED_X86_CONDITIONAL_RETURN_ADDR);
        let write = PcodeInstruction {
            address: address.clone(),
            op_code: OpCode::Copy,
            inputs: vec![VarnodeData::new(Address::new(register_space.clone(), 0), 4)],
            output: Some(VarnodeData::new(Address::new(ram_space.clone(), 0x4000), 4)),
        };
        let read = PcodeInstruction {
            address,
            op_code: OpCode::Copy,
            inputs: vec![VarnodeData::new(Address::new(ram_space, 0x4000), 4)],
            output: Some(VarnodeData::new(Address::new(register_space, 0), 4)),
        };

        assert_eq!(
            disassembler
                .translate_pcode_op(&write)
                .expect("fixed RAM write translation"),
            Some(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::constant(0x4000, address_size),
                val: Varnode::register(0, 4),
            })
        );
        assert_eq!(
            disassembler
                .translate_pcode_op(&read)
                .expect("fixed RAM read translation"),
            Some(R2ILOp::Load {
                dst: Varnode::register(0, 4),
                space: SpaceId::Ram,
                addr: Varnode::constant(0x4000, address_size),
            })
        );
    }

    #[test]
    fn callother_translation_preserves_numeric_id_and_operands() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 disassembler");
        let address_spaces = disassembler.address_spaces();
        let constant_space = address_spaces
            .iter()
            .find(|space| space.space_type == libsla::AddressSpaceType::Constant)
            .expect("constant space")
            .clone();
        let register_space = address_spaces
            .iter()
            .find(|space| space.name == "register")
            .expect("register space")
            .clone();
        let instruction = PcodeInstruction {
            address: Address::new(
                disassembler.default_code_space(),
                PINNED_X86_CONDITIONAL_RETURN_ADDR,
            ),
            op_code: OpCode::Pseudo(PseudoOp::CallOther),
            inputs: vec![
                VarnodeData::new(Address::new(constant_space.clone(), u32::MAX.into()), 4),
                VarnodeData::new(Address::new(constant_space, 0xfeed_face), 8),
            ],
            output: Some(VarnodeData::new(Address::new(register_space, 0), 8)),
        };

        assert_eq!(
            disassembler
                .translate_pcode_op(&instruction)
                .expect("CallOther translation"),
            Some(R2ILOp::CallOther {
                userop: u32::MAX,
                output: Some(Varnode::register(0, 8)),
                inputs: vec![Varnode::constant(0xfeed_face, 8)],
            })
        );
    }

    #[test]
    fn callother_translation_rejects_ids_that_do_not_fit_r2il() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 disassembler");
        let constant_space = disassembler
            .address_spaces()
            .into_iter()
            .find(|space| space.space_type == libsla::AddressSpaceType::Constant)
            .expect("constant space");
        let invalid_userop = u64::from(u32::MAX) + 1;
        let instruction = PcodeInstruction {
            address: Address::new(
                disassembler.default_code_space(),
                PINNED_X86_CONDITIONAL_RETURN_ADDR,
            ),
            op_code: OpCode::Pseudo(PseudoOp::CallOther),
            inputs: vec![VarnodeData::new(
                Address::new(constant_space, invalid_userop),
                8,
            )],
            output: None,
        };

        let error = disassembler
            .translate_pcode_op(&instruction)
            .expect_err("oversized CallOther id must be refused");
        assert_eq!(
            error.to_string(),
            format!("Unsupported feature: Sleigh CALLOTHER id does not fit r2il: {invalid_userop}")
        );
    }

    #[test]
    fn analysis_pcode_is_invalid_at_the_machine_lift_boundary() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 disassembler");
        let address = Address::new(
            disassembler.default_code_space(),
            PINNED_X86_CONDITIONAL_RETURN_ADDR,
        );

        for operation in [
            libsla::AnalysisOp::MultiEqual,
            libsla::AnalysisOp::CopyIndirect,
            libsla::AnalysisOp::PointerAdd,
            libsla::AnalysisOp::PointerSubcomponent,
            libsla::AnalysisOp::Cast,
            libsla::AnalysisOp::Insert,
            libsla::AnalysisOp::Extract,
            libsla::AnalysisOp::SegmentOp,
        ] {
            let instruction = PcodeInstruction {
                address: address.clone(),
                op_code: OpCode::Analysis(operation),
                inputs: Vec::new(),
                output: None,
            };
            assert!(
                matches!(
                    disassembler.translate_pcode_op(&instruction),
                    Err(LiftError::Unsupported(_))
                ),
                "analysis operation {operation:?} must be refused at the machine lift boundary"
            );
        }
    }

    #[test]
    fn unsupported_pcode_is_explicitly_refused() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 disassembler");
        let address = Address::new(
            disassembler.default_code_space(),
            PINNED_X86_CONDITIONAL_RETURN_ADDR,
        );

        for op_code in [
            OpCode::Pseudo(PseudoOp::ConstantPoolRef),
            OpCode::Pseudo(PseudoOp::New),
            OpCode::Unknown(i32::MAX),
        ] {
            let instruction = PcodeInstruction {
                address: address.clone(),
                op_code,
                inputs: Vec::new(),
                output: None,
            };
            assert!(
                matches!(
                    disassembler.translate_pcode_op(&instruction),
                    Err(LiftError::Unsupported(_))
                ),
                "unsupported {op_code:?} must never disappear from a canonical lift"
            );
        }
    }

    fn controlled_space(
        id: usize,
        name: &'static str,
        space_type: libsla::AddressSpaceType,
    ) -> AddressSpace {
        AddressSpace {
            id: AddressSpaceId::new(id),
            name: name.into(),
            word_size: 1,
            address_size: 8,
            space_type,
            big_endian: false,
        }
    }

    #[test]
    fn trusted_return_mechanism_validation_uses_only_exact_machine_facts() {
        let stack_pointer = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 64,
            size: 8,
        };
        let return_address = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 80,
            size: 8,
        };
        let without_mechanism = SourceFunctionInterface::new_exact(
            b"trusted-return-mechanism".to_vec(),
            "test-abi",
            [],
            r2source::SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(return_address))
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("exact machine roles");
        let exact = without_mechanism
            .clone()
            .with_exact_stacked_return(0, 8, 8, 8)
            .expect("canonical stacked return");
        let mut arch = r2il::ArchSpec::new("controlled-return-mechanism");
        arch.addr_size = 8;
        arch.add_register(r2il::RegisterDef::new("opaque-a", return_address.offset, 8));
        arch.add_register(r2il::RegisterDef::new("opaque-b", stack_pointer.offset, 8));
        arch.add_space(r2il::AddressSpace::ram(8));

        assert!(captured_return_mechanism_matches_arch(&exact, &arch));
        assert!(captured_return_mechanism_matches_arch(
            &without_mechanism,
            &arch
        ));

        arch.spaces[0].word_size = 2;
        assert!(!captured_return_mechanism_matches_arch(&exact, &arch));
        assert!(captured_return_mechanism_matches_arch(
            &without_mechanism,
            &arch
        ));
    }

    #[test]
    fn trusted_frame_pointer_validation_uses_only_exact_machine_facts() {
        let stack_pointer = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 64,
            size: 8,
        };
        let frame_pointer = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 72,
            size: 8,
        };
        let return_address = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 80,
            size: 8,
        };
        let absent = SourceFunctionInterface::new_exact(
            b"trusted-frame-pointer".to_vec(),
            "test-abi",
            [],
            r2source::SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(return_address))
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("exact machine roles");
        let exact = absent
            .clone()
            .with_frame_pointer_storage(frame_pointer)
            .expect("explicit frame-pointer role");
        let mut arch = r2il::ArchSpec::new("controlled-frame-pointer");
        arch.addr_size = 8;
        arch.add_register(r2il::RegisterDef::new("opaque-a", return_address.offset, 8));
        arch.add_register(r2il::RegisterDef::new("opaque-b", stack_pointer.offset, 8));
        arch.add_register(r2il::RegisterDef::new("opaque-c", frame_pointer.offset, 8));

        assert!(captured_frame_pointer_storage_matches_arch(&exact, &arch));
        assert!(captured_frame_pointer_storage_matches_arch(&absent, &arch));
        assert!(!is_exact_top_level_address_register(
            &arch,
            CanonicalStorageId {
                space: CanonicalStorageSpace::Ram,
                ..frame_pointer
            },
            8,
        ));

        arch.registers[2].parent = Some("missing-parent".to_string());
        assert!(!captured_frame_pointer_storage_matches_arch(&exact, &arch));
        assert!(captured_frame_pointer_storage_matches_arch(&absent, &arch));
        arch.registers[2].parent = None;
        arch.addr_size = 4;
        assert!(!captured_frame_pointer_storage_matches_arch(&exact, &arch));
        assert!(captured_frame_pointer_storage_matches_arch(&absent, &arch));
    }

    #[test]
    fn address_space_mapping_is_exact_and_collision_free() {
        use libsla::AddressSpaceType;

        let spaces = vec![
            controlled_space(1, "const", AddressSpaceType::Constant),
            controlled_space(2, "ram", AddressSpaceType::Processor),
            controlled_space(3, "register", AddressSpaceType::Processor),
            controlled_space(4, "unique", AddressSpaceType::Internal),
            controlled_space(5, "ab", AddressSpaceType::Processor),
            controlled_space(6, "ba", AddressSpaceType::Processor),
        ];
        let mut ctx = crate::context::LiftContext::new("controlled");
        let mapping =
            crate::sleigh::extract_address_space_map(&mut ctx, &spaces, AddressSpaceId::new(2))
                .expect("representable controlled address-space inventory");

        assert_eq!(mapping[&AddressSpaceId::new(1)], SpaceId::Const);
        assert_eq!(mapping[&AddressSpaceId::new(2)], SpaceId::Ram);
        assert_eq!(mapping[&AddressSpaceId::new(3)], SpaceId::Register);
        assert_eq!(mapping[&AddressSpaceId::new(4)], SpaceId::Unique);
        assert_eq!(mapping[&AddressSpaceId::new(5)], SpaceId::Custom(0));
        assert_eq!(mapping[&AddressSpaceId::new(6)], SpaceId::Custom(1));
        assert_ne!(
            mapping[&AddressSpaceId::new(5)],
            mapping[&AddressSpaceId::new(6)],
            "equal byte-sum names must not collide"
        );

        let ambiguous = vec![
            controlled_space(10, "ram", AddressSpaceType::Processor),
            controlled_space(11, "ram", AddressSpaceType::Processor),
        ];
        let mut ambiguous_ctx = crate::context::LiftContext::new("ambiguous");
        assert!(
            crate::sleigh::extract_address_space_map(
                &mut ambiguous_ctx,
                &ambiguous,
                AddressSpaceId::new(10),
            )
            .is_err(),
            "distinct Sleigh spaces that collapse to one r2il id are unrepresentable"
        );
    }

    #[test]
    fn trusted_space_map_matches_exported_architecture() {
        let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
            .expect("trusted x86-64 disassembler");
        let authority = disassembler
            .genuine_authority
            .as_ref()
            .expect("trusted profile authority");
        let spaces = disassembler.address_spaces();

        assert_eq!(spaces.len(), disassembler.space_map.len());
        for space in spaces {
            let mapped = disassembler
                .translate_space(&space)
                .expect("every trusted source space is mapped");
            let exported = authority
                .arch_spec()
                .spaces
                .iter()
                .find(|candidate| candidate.name.as_str() == space.name.as_ref())
                .expect("mapped space must be exported in the ArchSpec");
            assert_eq!(mapped, exported.id);
        }
    }

    #[test]
    fn function_layout_rejects_external_exits_inside_declared_ranges() {
        let range = GenuineFunctionBlockRange::new(0x1000, 0x20);
        assert!(
            GenuineFunctionLayout::new(b"revision".to_vec(), 0x1000, [range], [0x1010]).is_err()
        );
    }

    fn reg_name_resolver<'a>(
        map: &'a [(u64, u32, &'a str)],
    ) -> impl Fn(&Varnode) -> Option<String> + 'a {
        move |vn| {
            map.iter()
                .find(|(off, size, _)| *off == vn.offset && *size == vn.size)
                .map(|(_, _, name)| (*name).to_string())
        }
    }

    #[test]
    fn semantic_metadata_marks_pointer_and_stack_memory_class() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Load {
            dst: reg(0x10, 8),
            space: SpaceId::Ram,
            addr: reg(0x20, 8),
        });

        annotate_semantic_metadata_with_hints(
            &mut block,
            "x86-64",
            SemanticMetadataOptions::default(),
            reg_name_resolver(&[(0x10, 8, "rax"), (0x20, 8, "rsp")]),
        );

        let R2ILOp::Load { addr, .. } = &block.ops[0] else {
            panic!("expected load op");
        };
        let meta = addr.meta.as_ref().expect("address metadata");
        assert_eq!(meta.pointer_hint, Some(PointerHint::PointerLike));
        assert_eq!(meta.storage_class, Some(StorageClass::Stack));

        let op_meta = block.op_metadata(0).expect("load op metadata");
        assert_eq!(op_meta.memory_class, Some(MemoryClass::Stack));
        assert_eq!(
            op_meta.permissions,
            Some(MemoryPermissions {
                read: true,
                write: false,
                execute: false,
                volatile: false,
                cacheable: true,
            })
        );
    }

    #[test]
    fn semantic_metadata_marks_indirect_targets_as_code_pointers() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::CallInd {
            target: reg(0x30, 8),
        });

        annotate_semantic_metadata_with_hints(
            &mut block,
            "x86-64",
            SemanticMetadataOptions::default(),
            reg_name_resolver(&[(0x30, 8, "rax")]),
        );

        let R2ILOp::CallInd { target } = &block.ops[0] else {
            panic!("expected callind op");
        };
        let meta = target.meta.as_ref().expect("target metadata");
        assert_eq!(meta.pointer_hint, Some(PointerHint::CodePointer));
    }

    #[test]
    fn semantic_metadata_classifies_global_and_tls_memory() {
        let mut block = R2ILBlock::new(0x1000, 8);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: reg(0x40, 8),
            b: Varnode::constant(0x20, 8),
        });
        block.push(R2ILOp::Load {
            dst: reg(0x48, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        block.push(R2ILOp::Load {
            dst: reg(0x50, 8),
            space: SpaceId::Ram,
            addr: reg(0x60, 8),
        });

        annotate_semantic_metadata_with_hints(
            &mut block,
            "x86-64",
            SemanticMetadataOptions::default(),
            reg_name_resolver(&[
                (0x40, 8, "rip"),
                (0x48, 8, "rax"),
                (0x50, 8, "rbx"),
                (0x60, 8, "fs"),
            ]),
        );

        let R2ILOp::IntAdd { dst, .. } = &block.ops[0] else {
            panic!("expected intadd");
        };
        let dst_meta = dst.meta.as_ref().expect("tmp metadata");
        assert_eq!(dst_meta.storage_class, Some(StorageClass::Global));
        assert_eq!(dst_meta.pointer_hint, Some(PointerHint::PointerLike));

        let op_meta_global = block.op_metadata(1).expect("global load metadata");
        assert_eq!(op_meta_global.memory_class, Some(MemoryClass::Global));

        let op_meta_tls = block.op_metadata(2).expect("tls load metadata");
        assert_eq!(op_meta_tls.memory_class, Some(MemoryClass::ThreadLocal));
        assert_eq!(
            op_meta_tls.permissions,
            Some(MemoryPermissions {
                read: true,
                write: false,
                execute: false,
                volatile: false,
                cacheable: true,
            })
        );
    }

    #[test]
    fn semantic_metadata_generic_stack_fallback() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: reg(0x200, 8),
            val: reg(0x208, 8),
        });

        annotate_semantic_metadata_with_hints(
            &mut block,
            "riscv64",
            SemanticMetadataOptions::default(),
            reg_name_resolver(&[(0x200, 8, "sp"), (0x208, 8, "a0")]),
        );

        let op_meta = block.op_metadata(0).expect("store metadata");
        assert_eq!(op_meta.memory_class, Some(MemoryClass::Stack));
        assert_eq!(
            op_meta.permissions,
            Some(MemoryPermissions {
                read: false,
                write: true,
                execute: false,
                volatile: false,
                cacheable: true,
            })
        );
    }

    #[test]
    fn semantic_metadata_marks_mmio_permissions_as_volatile_non_cacheable() {
        let mut block = R2ILBlock::new(0x1000, 4);
        let mut src = reg(0x20, 8);
        src.meta = Some(r2il::VarnodeMetadata {
            storage_class: Some(StorageClass::Volatile),
            pointer_hint: Some(PointerHint::PointerLike),
            ..Default::default()
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x200, 8),
            src,
        });
        block.push(R2ILOp::Load {
            dst: reg(0x10, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x200, 8),
        });

        annotate_semantic_metadata_with_hints(
            &mut block,
            "x86-64",
            SemanticMetadataOptions::default(),
            reg_name_resolver(&[(0x10, 8, "rax"), (0x20, 8, "rsp")]),
        );

        let op_meta = block.op_metadata(1).expect("load metadata");
        assert_eq!(op_meta.memory_class, Some(MemoryClass::Mmio));
        assert_eq!(
            op_meta.permissions,
            Some(MemoryPermissions {
                read: true,
                write: false,
                execute: false,
                volatile: true,
                cacheable: false,
            })
        );
    }

    #[test]
    fn semantic_metadata_does_not_downgrade_existing_hints() {
        let mut block = R2ILBlock::new(0x1000, 4);
        let mut addr = reg(0x20, 8);
        addr.meta = Some(r2il::VarnodeMetadata {
            storage_class: Some(StorageClass::Global),
            pointer_hint: Some(PointerHint::CodePointer),
            ..Default::default()
        });
        block.push(R2ILOp::Load {
            dst: reg(0x10, 8),
            space: SpaceId::Ram,
            addr,
        });
        block.set_op_metadata(
            0,
            OpMetadata {
                memory_class: Some(MemoryClass::ThreadLocal),
                permissions: Some(MemoryPermissions {
                    read: true,
                    write: true,
                    execute: false,
                    volatile: true,
                    cacheable: false,
                }),
                ..Default::default()
            },
        );

        annotate_semantic_metadata_with_hints(
            &mut block,
            "x86-64",
            SemanticMetadataOptions::default(),
            reg_name_resolver(&[(0x10, 8, "rax"), (0x20, 8, "rsp")]),
        );

        let R2ILOp::Load { addr, .. } = &block.ops[0] else {
            panic!("expected load");
        };
        let meta = addr.meta.as_ref().expect("address metadata");
        assert_eq!(meta.storage_class, Some(StorageClass::Global));
        assert_eq!(meta.pointer_hint, Some(PointerHint::CodePointer));
        let op_meta = block.op_metadata(0).expect("existing op metadata");
        assert_eq!(op_meta.memory_class, Some(MemoryClass::ThreadLocal));
        assert_eq!(
            op_meta.permissions,
            Some(MemoryPermissions {
                read: true,
                write: true,
                execute: false,
                volatile: true,
                cacheable: false,
            })
        );
    }

    #[test]
    fn semantic_metadata_can_be_disabled() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Load {
            dst: reg(0x10, 8),
            space: SpaceId::Ram,
            addr: reg(0x20, 8),
        });

        annotate_semantic_metadata_with_hints(
            &mut block,
            "x86-64",
            SemanticMetadataOptions {
                enabled: false,
                ..Default::default()
            },
            reg_name_resolver(&[(0x10, 8, "rax"), (0x20, 8, "rsp")]),
        );

        let R2ILOp::Load { addr, .. } = &block.ops[0] else {
            panic!("expected load");
        };
        assert!(addr.meta.is_none(), "metadata should stay disabled");
        assert!(
            block.op_metadata.is_empty(),
            "op metadata should stay disabled"
        );
    }
}

#[cfg(all(test, feature = "x86"))]
mod sleigh_profile_load_cost {
    use super::*;

    /// What loading a profile costs against what lifting costs, which is the
    /// measurement that moved the profile load out of the per-function path.
    ///
    /// Not a gate: it prints rather than asserts, because a wall-clock bound
    /// checked in CI is a flake and the ratio is the finding. Run it with
    /// `cargo test --release -p r2sleigh-lift --features x86
    /// sleigh_profile_load_cost -- --ignored --nocapture`.
    #[test]
    #[ignore = "measurement, not a gate"]
    fn loading_a_profile_costs_a_thousand_lifts() {
        for round in 0..3 {
            let started = std::time::Instant::now();
            let cold = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
                .expect("x86-64 profile");
            eprintln!(
                "round {round}: cold load = {}us",
                started.elapsed().as_micros()
            );
            let started = std::time::Instant::now();
            let _ = cold.lift_genuine_block(&[0x48, 0x89, 0xe5], 0x1000, 3);
            eprintln!(
                "round {round}: one three-byte block = {}us",
                started.elapsed().as_micros()
            );
            let started = std::time::Instant::now();
            let shared = Disassembler::shared_trusted_profile(TrustedSleighProfile::X86_64)
                .expect("shared x86-64 profile");
            eprintln!(
                "round {round}: shared load = {}us",
                started.elapsed().as_micros()
            );
            assert_eq!(shared.trusted_profile, Some(TrustedSleighProfile::X86_64));
        }
    }

    #[test]
    fn one_profile_is_loaded_once_and_handed_out_again() {
        let first =
            Disassembler::shared_trusted_profile(TrustedSleighProfile::X86_64).expect("first ask");
        let second =
            Disassembler::shared_trusted_profile(TrustedSleighProfile::X86_64).expect("second ask");
        assert!(
            Rc::ptr_eq(&first, &second),
            "the second ask must be the same loaded profile, not another copy"
        );
        assert_eq!(first.trusted_profile, Some(TrustedSleighProfile::X86_64));
        assert!(first.genuine_authority.is_some());
    }
}
