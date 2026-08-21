//! Immutable machine context captured with an SSA artifact.
//!
//! Legacy `SSAOp` memory-space strings are presentation data and cannot serve
//! as proof. This snapshot retains the typed r2il address space at each source
//! operation site together with the architecture memory model used to lift it.

use std::collections::{BTreeMap, BTreeSet};

use r2il::{ArchSpec, Endianness, R2ILBlock, R2ILOp, SpaceId, effective_arch_address_size};
use serde::Serialize;

use crate::function::SSAFunction;
use crate::op::SSAOp;
use crate::semantic::CallSiteId;
pub use r2source::{
    CanonicalStorageId, CanonicalStorageSpace, SOURCE_CALL_SITE_INTERFACE_SCHEMA_VERSION,
    SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION, SOURCE_TYPE_GRAPH_SCHEMA_VERSION,
    SourceAbiParameterSpec, SourceAggregateLayout, SourceAggregateMember, SourceCallArgumentSpec,
    SourceCallResult, SourceCallSiteIdentity, SourceCallSiteInterface,
    SourceCallSiteInterfaceError, SourceCarrierKind, SourceCarrierProjection,
    SourceFunctionInterface, SourceFunctionInterfaceError, SourceFunctionReturn,
    SourceLogicalValue, SourceMachineRoles,
    SourceConventionSlots, SourceStackAllocationContract, SourceStackGrowth,
    SourceStackSlotRole, SourceStackSlotSpec, SourceType, SourceTypeGraph, SourceTypeGraphError,
    SourceTypeKind, StackAddressBase,
};

pub const MACHINE_CONTEXT_SCHEMA_VERSION: u32 = 16;

/// Canonical architecture family captured from the exact lifting profile.
///
/// This is semantic source identity, unlike calling-convention or register
/// presentation strings. Unknown families remain explicit so architecture-
/// specific consumers can fail closed.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize)]
pub enum MachineArchitectureFamily {
    #[default]
    Unknown,
    X86,
    X86_64,
    Arm,
    AArch64,
    RiscV32,
    RiscV64,
    Mips32,
    Mips64,
    PowerPc32,
    PowerPc64,
}

impl MachineArchitectureFamily {
    /// Project an architecture description into the same typed family used by
    /// immutable machine-context authority.
    pub fn from_arch_spec(arch: Option<&ArchSpec>) -> Self {
        let Some(arch) = arch else {
            return Self::Unknown;
        };
        let name = arch.name.trim().to_ascii_lowercase();
        let address_size = effective_arch_address_size(arch);
        if matches!(name.as_str(), "x86-64" | "x86_64" | "x64" | "amd64")
            || ((name == "x86" || name.starts_with("x86:")) && address_size == 8)
        {
            Self::X86_64
        } else if matches!(name.as_str(), "x86-32" | "i386" | "i686")
            || ((name == "x86" || name.starts_with("x86:")) && address_size == 4)
        {
            Self::X86
        } else if name == "aarch64"
            || name == "arm64"
            || name.starts_with("aarch64:")
            || name.starts_with("arm64:")
        {
            Self::AArch64
        } else if (name == "arm" || name.starts_with("arm:")) && address_size == 4
            || name.starts_with("armv")
        {
            Self::Arm
        } else if name == "riscv32"
            || name == "rv32"
            || name.starts_with("rv32")
            || ((name == "riscv" || name.starts_with("riscv:")) && address_size == 4)
        {
            Self::RiscV32
        } else if name == "riscv64"
            || name == "rv64"
            || name.starts_with("rv64")
            || ((name == "riscv" || name.starts_with("riscv:")) && address_size == 8)
        {
            Self::RiscV64
        } else if (name == "mips" || name.starts_with("mips:") || name.starts_with("mips32"))
            && address_size == 4
        {
            Self::Mips32
        } else if name.starts_with("mips64")
            || ((name == "mips" || name.starts_with("mips:")) && address_size == 8)
        {
            Self::Mips64
        } else if (name == "ppc" || name.starts_with("ppc:") || name.starts_with("powerpc"))
            && address_size == 4
        {
            Self::PowerPc32
        } else if name.starts_with("ppc64")
            || ((name == "ppc" || name.starts_with("ppc:") || name.starts_with("powerpc"))
                && address_size == 8)
        {
            Self::PowerPc64
        } else {
            Self::Unknown
        }
    }
}
/// One canonical register carrier in the immutable ABI snapshot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct MachineAbiRegisterSlot {
    index: u32,
    storage: CanonicalStorageId,
}

impl MachineAbiRegisterSlot {
    pub const fn index(&self) -> u32 {
        self.index
    }

    pub const fn storage(&self) -> CanonicalStorageId {
        self.storage
    }
}

/// Typed calling-convention carrier snapshot injected with the function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MachineAbiModel {
    schema_version: u32,
    available: bool,
    coherent: bool,
    argument_registers: Box<[MachineAbiRegisterSlot]>,
    return_registers: Box<[MachineAbiRegisterSlot]>,
    frame_pointer_storage: Option<CanonicalStorageId>,
}

impl MachineAbiModel {
    fn unavailable() -> Self {
        Self {
            schema_version: MACHINE_CONTEXT_SCHEMA_VERSION,
            available: false,
            coherent: false,
            argument_registers: Box::new([]),
            return_registers: Box::new([]),
            frame_pointer_storage: None,
        }
    }

    fn from_interface(
        interface: Option<&SourceFunctionInterface>,
        frame_pointer_storage: Option<CanonicalStorageId>,
    ) -> Self {
        let Some(interface) = interface else {
            return Self::unavailable();
        };
        let argument_registers = interface
            .parameters()
            .iter()
            .map(|parameter| MachineAbiRegisterSlot {
                index: parameter.index(),
                storage: parameter.storage(),
            })
            .collect::<Vec<_>>();
        let return_registers = match interface.return_kind() {
            SourceFunctionReturn::Void => Vec::new(),
            SourceFunctionReturn::Register { storage } => {
                vec![MachineAbiRegisterSlot { index: 0, storage }]
            }
        };
        Self {
            schema_version: MACHINE_CONTEXT_SCHEMA_VERSION,
            available: true,
            coherent: true,
            argument_registers: argument_registers.into_boxed_slice(),
            return_registers: return_registers.into_boxed_slice(),
            frame_pointer_storage,
        }
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn is_available(&self) -> bool {
        self.available
    }

    pub const fn is_coherent(&self) -> bool {
        self.coherent
    }

    pub const fn argument_registers(&self) -> &[MachineAbiRegisterSlot] {
        &self.argument_registers
    }

    pub const fn return_registers(&self) -> &[MachineAbiRegisterSlot] {
        &self.return_registers
    }

    pub const fn frame_pointer_storage(&self) -> Option<CanonicalStorageId> {
        self.frame_pointer_storage
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum MachineMemoryEndianness {
    Little,
    Big,
    Mixed,
    Custom,
    Unknown,
}

impl From<Endianness> for MachineMemoryEndianness {
    fn from(endianness: Endianness) -> Self {
        match endianness {
            Endianness::Little => Self::Little,
            Endianness::Big => Self::Big,
            Endianness::Mixed => Self::Mixed,
            Endianness::Custom => Self::Custom,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MachineMemorySpace {
    space: SpaceId,
    address_bits: u32,
    word_size_bytes: u32,
    endianness: MachineMemoryEndianness,
}

impl MachineMemorySpace {
    pub const fn space(&self) -> SpaceId {
        self.space
    }

    pub const fn address_bits(&self) -> u32 {
        self.address_bits
    }

    pub const fn word_size_bytes(&self) -> u32 {
        self.word_size_bytes
    }

    pub const fn endianness(&self) -> MachineMemoryEndianness {
        self.endianness
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MachineMemoryModel {
    schema_version: u32,
    available: bool,
    coherent: bool,
    default_address_bits: u32,
    alignment_bytes: u32,
    default_endianness: MachineMemoryEndianness,
    spaces: Box<[MachineMemorySpace]>,
}

impl MachineMemoryModel {
    fn unavailable() -> Self {
        Self {
            schema_version: MACHINE_CONTEXT_SCHEMA_VERSION,
            available: false,
            coherent: false,
            default_address_bits: 0,
            alignment_bytes: 0,
            default_endianness: MachineMemoryEndianness::Unknown,
            spaces: Box::new([]),
        }
    }

    fn from_arch(arch: Option<&ArchSpec>) -> Self {
        let Some(arch) = arch else {
            return Self::unavailable();
        };
        let effective_address_size = effective_arch_address_size(arch);
        let default_address_bits = effective_address_size.checked_mul(8).unwrap_or(0);
        let mut coherent = default_address_bits > 0 && arch.alignment > 0;
        let default_endianness = MachineMemoryEndianness::from(arch.memory_endianness);
        let mut spaces = Vec::with_capacity(arch.spaces.len() + 1);

        for source in &arch.spaces {
            if spaces
                .iter()
                .any(|space: &MachineMemorySpace| space.space == source.id)
            {
                coherent = false;
                continue;
            }
            let address_size = if source.addr_size > 1 {
                source.addr_size
            } else {
                effective_address_size
            };
            let address_bits = address_size.checked_mul(8).unwrap_or(0);
            if address_bits == 0 || source.word_size == 0 {
                coherent = false;
            }
            spaces.push(MachineMemorySpace {
                space: source.id,
                address_bits,
                word_size_bytes: source.word_size,
                endianness: source
                    .endianness
                    .map(MachineMemoryEndianness::from)
                    .unwrap_or(default_endianness),
            });
        }
        if !spaces.iter().any(|space| space.space == SpaceId::Ram) {
            spaces.push(MachineMemorySpace {
                space: SpaceId::Ram,
                address_bits: default_address_bits,
                word_size_bytes: 1,
                endianness: default_endianness,
            });
        }
        spaces.sort_by_key(|space| space_sort_key(space.space));

        Self {
            schema_version: MACHINE_CONTEXT_SCHEMA_VERSION,
            available: true,
            coherent,
            default_address_bits,
            alignment_bytes: arch.alignment,
            default_endianness,
            spaces: spaces.into_boxed_slice(),
        }
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn is_available(&self) -> bool {
        self.available
    }

    pub const fn is_coherent(&self) -> bool {
        self.coherent
    }

    pub const fn default_address_bits(&self) -> u32 {
        self.default_address_bits
    }

    pub const fn alignment_bytes(&self) -> u32 {
        self.alignment_bytes
    }

    pub const fn default_endianness(&self) -> MachineMemoryEndianness {
        self.default_endianness
    }

    pub const fn spaces(&self) -> &[MachineMemorySpace] {
        &self.spaces
    }

    pub fn space(&self, space: SpaceId) -> Option<&MachineMemorySpace> {
        self.spaces
            .iter()
            .find(|candidate| candidate.space == space)
    }
}

fn is_exact_top_level_address_register(
    arch: &ArchSpec,
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

fn frame_pointer_storage_matches_machine(
    interface: &SourceFunctionInterface,
    frame_pointer_storage: Option<CanonicalStorageId>,
    arch: Option<&ArchSpec>,
) -> bool {
    let Some(frame_pointer) = frame_pointer_storage else {
        return true;
    };
    let Some(arch) = arch else {
        return false;
    };
    let Some(return_address) = interface.return_address_storage() else {
        return false;
    };
    let Some(stack_pointer) = interface.stack_pointer_storage() else {
        return false;
    };
    let address_size = effective_arch_address_size(arch);
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

fn return_mechanism_matches_machine(
    interface: &SourceFunctionInterface,
    arch: Option<&ArchSpec>,
    memory_model: &MachineMemoryModel,
) -> bool {
    let Some(mechanism) = interface.return_mechanism() else {
        return true;
    };
    let Some(arch) = arch else {
        return false;
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
        || memory_model.default_address_bits() != address_bits
    {
        return false;
    }
    let Some(ram) = memory_model.space(SpaceId::Ram) else {
        return false;
    };
    if ram.word_size_bytes() != 1 || ram.address_bits() != address_bits {
        return false;
    }
    let mut explicit_ram_spaces = arch.spaces.iter().filter(|space| space.id == SpaceId::Ram);
    let Some(explicit_ram) = explicit_ram_spaces.next() else {
        return false;
    };
    if explicit_ram_spaces.next().is_some()
        || explicit_ram.word_size != 1
        || explicit_ram.addr_size != address_size
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SourceMachineContext {
    schema_version: u32,
    architecture_family: MachineArchitectureFamily,
    memory_model: MachineMemoryModel,
    function_interface: Option<SourceFunctionInterface>,
    machine_roles: SourceMachineRoles,
    /// Where this convention would leave arguments and a result. The result
    /// slot is what makes "is this the return register" answerable without a
    /// list of register spellings.
    convention_slots: Option<SourceConventionSlots>,
    abi_model: MachineAbiModel,
    register_storages_by_name: BTreeMap<String, CanonicalStorageId>,
    raw_call_sites_by_id: BTreeMap<CallSiteId, SourceCallSiteIdentity>,
    call_site_interfaces: BTreeMap<SourceCallSiteIdentity, SourceCallSiteInterface>,
    memory_spaces_by_op: BTreeMap<(u64, usize), SpaceId>,
}

struct MachineContextIdentityWriter(Vec<u8>);

impl MachineContextIdentityWriter {
    fn new() -> Self {
        Self(Vec::new())
    }

    fn u8(&mut self, value: u8) {
        self.0.push(value);
    }

    fn bool(&mut self, value: bool) {
        self.u8(u8::from(value));
    }

    fn u32(&mut self, value: u32) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }

    fn i64(&mut self, value: i64) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }

    fn usize(&mut self, value: usize) {
        self.u64(value as u64);
    }

    fn bytes(&mut self, value: &[u8]) {
        self.usize(value.len());
        self.0.extend_from_slice(value);
    }

    fn string(&mut self, value: &str) {
        self.bytes(value.as_bytes());
    }

    fn storage(&mut self, storage: CanonicalStorageId) {
        self.u8(match storage.space {
            CanonicalStorageSpace::Ram => 1,
            CanonicalStorageSpace::Register => 2,
            CanonicalStorageSpace::Unique => 3,
            CanonicalStorageSpace::Constant => 4,
            CanonicalStorageSpace::Custom(_) => 5,
            CanonicalStorageSpace::Unknown => 6,
        });
        if let CanonicalStorageSpace::Custom(id) = storage.space {
            self.u32(id);
        }
        self.u64(storage.offset);
        self.u32(storage.size);
    }

    fn option_storage(&mut self, storage: Option<CanonicalStorageId>) {
        match storage {
            Some(storage) => {
                self.u8(1);
                self.storage(storage);
            }
            None => self.u8(0),
        }
    }

    fn space(&mut self, space: SpaceId) {
        self.u8(match space {
            SpaceId::Ram => 1,
            SpaceId::Register => 2,
            SpaceId::Unique => 3,
            SpaceId::Const => 4,
            SpaceId::Custom(_) => 5,
        });
        if let SpaceId::Custom(id) = space {
            self.u32(id);
        }
    }

    fn stack_base(&mut self, base: StackAddressBase) {
        self.u8(match base {
            StackAddressBase::StackPointer => 1,
            StackAddressBase::FramePointer => 2,
        });
    }

    fn logical_value(&mut self, value: SourceLogicalValue) {
        self.u32(value.type_id());
        let carrier = value.carrier();
        self.u8(match carrier.kind() {
            SourceCarrierKind::Full => 1,
            SourceCarrierKind::LowBits => 2,
        });
        self.u64(carrier.offset_bits());
        self.u64(carrier.size_bits());
    }

    fn finish(self) -> Box<[u8]> {
        self.0.into_boxed_slice()
    }
}

fn write_memory_endianness(
    writer: &mut MachineContextIdentityWriter,
    endianness: MachineMemoryEndianness,
) {
    writer.u8(match endianness {
        MachineMemoryEndianness::Little => 1,
        MachineMemoryEndianness::Big => 2,
        MachineMemoryEndianness::Mixed => 3,
        MachineMemoryEndianness::Custom => 4,
        MachineMemoryEndianness::Unknown => 5,
    });
}

fn write_return_mechanism(
    writer: &mut MachineContextIdentityWriter,
    mechanism: Option<r2source::SourceReturnMechanism>,
) {
    match mechanism {
        Some(r2source::SourceReturnMechanism::Stacked {
            stack_offset,
            slot_size_bytes,
            stack_pointer_delta_bytes,
            address_size_bytes,
        }) => {
            writer.u8(1);
            writer.i64(stack_offset);
            writer.u32(slot_size_bytes);
            writer.u32(stack_pointer_delta_bytes);
            writer.u32(address_size_bytes);
        }
        None => writer.u8(0),
    }
}

fn write_type_graph(writer: &mut MachineContextIdentityWriter, graph: Option<&SourceTypeGraph>) {
    let Some(graph) = graph else {
        writer.u8(0);
        return;
    };
    writer.u8(1);
    writer.u32(graph.schema_version());
    writer.usize(graph.types().len());
    for source_type in graph.types() {
        writer.u32(source_type.id());
        match source_type.kind() {
            SourceTypeKind::SignedInteger => writer.u8(1),
            SourceTypeKind::UnsignedInteger => writer.u8(2),
            SourceTypeKind::Pointer { target_type_id } => {
                writer.u8(3);
                writer.u32(target_type_id);
            }
            SourceTypeKind::Struct { aggregate_id } => {
                writer.u8(4);
                writer.u32(aggregate_id);
            }
        }
        writer.u64(source_type.size_bits());
        writer.u64(source_type.align_bits());
    }
    writer.usize(graph.aggregates().len());
    for aggregate in graph.aggregates() {
        writer.u32(aggregate.id());
        writer.u32(aggregate.type_id());
        writer.u64(aggregate.size_bits());
        writer.u64(aggregate.align_bits());
        writer.usize(aggregate.members().len());
        for member in aggregate.members() {
            writer.u32(member.member_id());
            writer.u32(member.type_id());
            writer.u64(member.offset_bits());
            writer.u64(member.size_bits());
        }
    }
}

fn write_function_interface(
    writer: &mut MachineContextIdentityWriter,
    interface: Option<&SourceFunctionInterface>,
) {
    let Some(interface) = interface else {
        writer.u8(0);
        return;
    };
    writer.u8(1);
    writer.u32(interface.schema_version());
    writer.bytes(interface.revision_identity());
    writer.string(interface.calling_convention());
    writer.usize(interface.parameters().len());
    for parameter in interface.parameters() {
        writer.u32(parameter.index());
        writer.storage(parameter.storage());
    }
    match interface.return_kind() {
        SourceFunctionReturn::Void => writer.u8(0),
        SourceFunctionReturn::Register { storage } => {
            writer.u8(1);
            writer.storage(storage);
        }
    }
    writer.option_storage(interface.return_address_storage());
    writer.option_storage(interface.stack_pointer_storage());
    writer.option_storage(interface.frame_pointer_storage());
    write_return_mechanism(writer, interface.return_mechanism());
    match interface.stack_allocation_contract() {
        Some(contract) => {
            writer.u8(1);
            writer.u8(match contract.growth() {
                SourceStackGrowth::LowerAddresses => 1,
                SourceStackGrowth::HigherAddresses => 2,
            });
            writer.u32(contract.implicit_active_sp_bytes());
        }
        None => writer.u8(0),
    }
    writer.usize(interface.stack_slots().len());
    for slot in interface.stack_slots() {
        writer.stack_base(slot.base());
        writer.storage(slot.base_storage());
        writer.i64(slot.offset());
        writer.u32(slot.size_bytes());
        match slot.role() {
            SourceStackSlotRole::UnclassifiedResource => writer.u8(1),
            SourceStackSlotRole::Local => writer.u8(2),
            SourceStackSlotRole::ParameterHome {
                parameter_index,
                home_storage,
            } => {
                writer.u8(3);
                writer.u32(parameter_index);
                writer.storage(home_storage);
            }
        }
    }
    writer.usize(interface.parameter_logical_values().len());
    for value in interface.parameter_logical_values() {
        writer.logical_value(*value);
    }
    match interface.return_logical_value() {
        Some(value) => {
            writer.u8(1);
            writer.logical_value(value);
        }
        None => writer.u8(0),
    }
    write_type_graph(writer, interface.type_graph());
    writer.bool(interface.stack_slot_roles_complete());
}

fn write_call_identity(
    writer: &mut MachineContextIdentityWriter,
    identity: SourceCallSiteIdentity,
) {
    writer.u64(identity.block_addr());
    writer.usize(identity.op_index());
    writer.storage(identity.target());
}

fn write_call_site_interface(
    writer: &mut MachineContextIdentityWriter,
    interface: &SourceCallSiteInterface,
) {
    writer.u32(interface.schema_version());
    writer.bytes(interface.revision_identity());
    write_call_identity(writer, interface.identity());
    writer.bool(interface.is_complete());
    writer.string(interface.calling_convention());
    writer.usize(interface.arguments().len());
    for argument in interface.arguments() {
        writer.u32(argument.index());
        writer.storage(argument.storage());
    }
    writer.bool(interface.is_variadic());
    writer.bool(interface.is_noreturn());
    match interface.result() {
        SourceCallResult::Void => writer.u8(0),
        SourceCallResult::Register { storage } => {
            writer.u8(1);
            writer.storage(storage);
        }
    }
}

impl SourceMachineContext {
    pub(crate) fn from_blocks(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Self {
        Self::from_blocks_with_interfaces(
            blocks,
            arch,
            None,
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        )
    }

    pub(crate) fn from_blocks_with_interfaces(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        function_interface: Option<SourceFunctionInterface>,
        machine_roles: SourceMachineRoles,
        convention_slots: Option<SourceConventionSlots>,
        call_site_interfaces: Vec<SourceCallSiteInterface>,
    ) -> Self {
        let register_storages_by_name: BTreeMap<String, CanonicalStorageId> = arch
            .into_iter()
            .flat_map(|arch| &arch.registers)
            .map(|register| {
                (
                    register.name.to_ascii_lowercase(),
                    CanonicalStorageId {
                        space: CanonicalStorageSpace::Register,
                        offset: register.offset,
                        size: register.size,
                    },
                )
            })
            .collect();
        let architecture_family = MachineArchitectureFamily::from_arch_spec(arch);
        let memory_model = MachineMemoryModel::from_arch(arch);
        let frame_pointer_storage = function_interface
            .as_ref()
            .and_then(SourceFunctionInterface::exact_frame_pointer_storage);
        let mut abi_model =
            MachineAbiModel::from_interface(function_interface.as_ref(), frame_pointer_storage);
        if let Some(interface) = function_interface.as_ref() {
            let has_frame_pointer_slots = interface
                .stack_slots()
                .iter()
                .any(|slot| slot.base() == StackAddressBase::FramePointer);
            let exact_interface_roles_exist = interface.stack_slot_roles_complete()
                && interface.return_address_storage().is_some()
                && interface.stack_pointer_storage().is_some()
                && (!has_frame_pointer_slots || frame_pointer_storage.is_some());
            let carrier_storages_are_disjoint = interface
                .return_address_storage()
                .is_none_or(|storage| interface.return_address_storage_is_valid(storage))
                && interface
                    .stack_pointer_storage()
                    .is_none_or(|storage| interface.stack_pointer_storage_is_valid(storage));
            let declared_storages_exist = interface
                .parameters()
                .iter()
                .map(SourceAbiParameterSpec::storage)
                .chain(match interface.return_kind() {
                    SourceFunctionReturn::Void => None,
                    SourceFunctionReturn::Register { storage } => Some(storage),
                })
                .chain(
                    interface
                        .stack_slots()
                        .iter()
                        .map(SourceStackSlotSpec::base_storage),
                )
                .chain(interface.return_address_storage())
                .chain(interface.stack_pointer_storage())
                .chain(frame_pointer_storage)
                .all(|storage| {
                    register_storages_by_name
                        .values()
                        .any(|actual| *actual == storage)
                });
            let is_exact_address_register = |storage: CanonicalStorageId| {
                arch.is_some_and(|arch| {
                    is_exact_top_level_address_register(
                        arch,
                        storage,
                        effective_arch_address_size(arch),
                    )
                })
            };
            let machine_carriers_are_exact_address_registers = interface
                .return_address_storage()
                .is_none_or(is_exact_address_register)
                && interface
                    .stack_pointer_storage()
                    .is_none_or(is_exact_address_register)
                && frame_pointer_storage.is_none_or(is_exact_address_register);
            abi_model.coherent &= exact_interface_roles_exist
                && carrier_storages_are_disjoint
                && declared_storages_exist
                && machine_carriers_are_exact_address_registers
                && frame_pointer_storage_matches_machine(interface, frame_pointer_storage, arch)
                && return_mechanism_matches_machine(interface, arch, &memory_model);
        }
        let raw_call_sites_by_id = collect_raw_call_site_identities(blocks);
        let raw_call_sites = raw_call_sites_by_id
            .values()
            .copied()
            .collect::<BTreeSet<_>>();
        let expected_call_site_revision = function_interface
            .as_ref()
            .map(|interface| interface.revision_identity().to_vec().into_boxed_slice())
            .or_else(|| {
                call_site_interfaces
                    .first()
                    .map(|interface| interface.revision_identity().to_vec().into_boxed_slice())
            });
        let mut call_site_interfaces_by_identity = BTreeMap::new();
        let mut claimed_sites = BTreeSet::new();
        for interface in call_site_interfaces {
            let identity = interface.identity();
            let site = (identity.block_addr(), identity.op_index());
            let carriers_exist = interface
                .arguments()
                .iter()
                .map(|argument| argument.storage())
                .chain(match interface.result() {
                    SourceCallResult::Void => None,
                    SourceCallResult::Register { storage } => Some(storage),
                })
                .all(|storage| {
                    register_storages_by_name
                        .values()
                        .any(|actual| *actual == storage)
                });
            // A call site the source described badly says nothing about the
            // other call sites in this function. Drop the one that does not
            // hold up and keep the rest, rather than withholding every
            // interface because one of them was wrong: interfaces are already
            // stored per identity, so there is nothing shared to protect.
            if interface.schema_version() != SOURCE_CALL_SITE_INTERFACE_SCHEMA_VERSION
                || expected_call_site_revision.as_deref() != Some(interface.revision_identity())
                || !raw_call_sites.contains(&identity)
                || !claimed_sites.insert(site)
                || !carriers_exist
            {
                call_site_interfaces_by_identity.remove(&identity);
                continue;
            }
            if call_site_interfaces_by_identity
                .insert(identity, interface)
                .is_some()
            {
                // Two interfaces claiming one identity leave no way to tell
                // which describes the call, so neither is kept.
                call_site_interfaces_by_identity.remove(&identity);
            }
        }
        let memory_spaces_by_op = blocks
            .iter()
            .flat_map(|block| {
                block
                    .ops
                    .iter()
                    .enumerate()
                    .filter_map(move |(op_index, op)| {
                        memory_space(op).map(|space| ((block.addr, op_index), space))
                    })
            })
            .collect();
        Self {
            schema_version: MACHINE_CONTEXT_SCHEMA_VERSION,
            architecture_family,
            memory_model,
            function_interface,
            machine_roles,
            convention_slots,
            abi_model,
            register_storages_by_name,
            raw_call_sites_by_id,
            call_site_interfaces: call_site_interfaces_by_identity,
            memory_spaces_by_op,
        }
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn architecture_family(&self) -> MachineArchitectureFamily {
        self.architecture_family
    }

    pub const fn memory_model(&self) -> &MachineMemoryModel {
        &self.memory_model
    }

    pub const fn abi_model(&self) -> &MachineAbiModel {
        &self.abi_model
    }

    pub const fn function_interface(&self) -> Option<&SourceFunctionInterface> {
        self.function_interface.as_ref()
    }

    /// Borrow the machine carriers the source resolved from its register
    /// profile. These are available whether or not an ABI was recovered.
    pub const fn machine_roles(&self) -> &SourceMachineRoles {
        &self.machine_roles
    }

    /// The location this convention leaves a result in, when the source said.
    pub fn result_slot(&self) -> Option<CanonicalStorageId> {
        self.convention_slots.as_ref()?.result_slot()
    }

    /// The location this function returns a value in, and whether it returns
    /// one at all.
    ///
    /// The interface states both, so a function declared to return nothing
    /// answers `None` rather than the location a result would have gone in.
    /// The convention answers only where a caller *would* leave a value, which
    /// is not the same claim, so it is the fallback for a function whose
    /// interface was never recovered.
    pub fn return_value_carrier(&self) -> Option<CanonicalStorageId> {
        match self.function_interface.as_ref().map(|i| i.return_kind()) {
            Some(r2source::SourceFunctionReturn::Void) => None,
            Some(r2source::SourceFunctionReturn::Register { storage }) => Some(storage),
            None => self.result_slot(),
        }
    }

    /// The carrier holding the return address, preferring the ABI's own
    /// declaration and falling back to the machine's.
    ///
    /// Both name the same register when both exist, which the source enforces
    /// when it captures them; the fallback is what keeps this answerable for a
    /// function whose ABI was never recovered.
    pub fn return_address_carrier(&self) -> Option<CanonicalStorageId> {
        self.function_interface
            .as_ref()
            .and_then(|interface| interface.return_address_storage())
            .or_else(|| self.machine_roles.return_address_storage())
    }

    /// The carrier holding the stack pointer, resolved like
    /// [`Self::return_address_carrier`].
    pub fn stack_pointer_carrier(&self) -> Option<CanonicalStorageId> {
        self.function_interface
            .as_ref()
            .and_then(|interface| interface.stack_pointer_storage())
            .or_else(|| self.machine_roles.stack_pointer_storage())
    }

    pub const fn return_mechanism(&self) -> Option<r2source::SourceReturnMechanism> {
        match self.function_interface.as_ref() {
            Some(interface) => interface.return_mechanism(),
            None => None,
        }
    }

    pub fn register_storage(&self, name: &str) -> Option<CanonicalStorageId> {
        self.register_storages_by_name
            .get(&name.to_ascii_lowercase())
            .copied()
    }

    pub const fn register_storages_by_name(&self) -> &BTreeMap<String, CanonicalStorageId> {
        &self.register_storages_by_name
    }

    pub const fn raw_call_sites_by_id(&self) -> &BTreeMap<CallSiteId, SourceCallSiteIdentity> {
        &self.raw_call_sites_by_id
    }

    pub fn raw_call_site_identity(&self, call_site: CallSiteId) -> Option<SourceCallSiteIdentity> {
        self.raw_call_sites_by_id.get(&call_site).copied()
    }

    pub const fn call_site_interfaces(
        &self,
    ) -> &BTreeMap<SourceCallSiteIdentity, SourceCallSiteInterface> {
        &self.call_site_interfaces
    }

    pub fn call_site_interface(&self, call_site: CallSiteId) -> Option<&SourceCallSiteInterface> {
        self.raw_call_site_identity(call_site)
            .and_then(|identity| self.call_site_interfaces.get(&identity))
    }

    pub fn memory_space_at(&self, block_addr: u64, op_index: usize) -> Option<SpaceId> {
        self.memory_spaces_by_op
            .get(&(block_addr, op_index))
            .copied()
    }

    pub const fn memory_spaces_by_op(&self) -> &BTreeMap<(u64, usize), SpaceId> {
        &self.memory_spaces_by_op
    }

    /// Canonical, presentation-independent identity of every immutable
    /// machine/source fact that can affect prepared semantics or certification.
    pub(crate) fn semantic_identity_bytes(&self) -> Box<[u8]> {
        let mut writer = MachineContextIdentityWriter::new();
        writer.bytes(b"r2ssa-machine-context-semantic-v2");
        writer.u32(self.schema_version);
        writer.u8(match self.architecture_family {
            MachineArchitectureFamily::Unknown => 0,
            MachineArchitectureFamily::X86 => 1,
            MachineArchitectureFamily::X86_64 => 2,
            MachineArchitectureFamily::Arm => 3,
            MachineArchitectureFamily::AArch64 => 4,
            MachineArchitectureFamily::RiscV32 => 5,
            MachineArchitectureFamily::RiscV64 => 6,
            MachineArchitectureFamily::Mips32 => 7,
            MachineArchitectureFamily::Mips64 => 8,
            MachineArchitectureFamily::PowerPc32 => 9,
            MachineArchitectureFamily::PowerPc64 => 10,
        });

        let memory = &self.memory_model;
        writer.u32(memory.schema_version());
        writer.bool(memory.is_available());
        writer.bool(memory.is_coherent());
        writer.u32(memory.default_address_bits());
        writer.u32(memory.alignment_bytes());
        write_memory_endianness(&mut writer, memory.default_endianness());
        writer.usize(memory.spaces().len());
        for space in memory.spaces() {
            writer.space(space.space());
            writer.u32(space.address_bits());
            writer.u32(space.word_size_bytes());
            write_memory_endianness(&mut writer, space.endianness());
        }

        let abi = &self.abi_model;
        writer.u32(abi.schema_version());
        writer.bool(abi.is_available());
        writer.bool(abi.is_coherent());
        writer.usize(abi.argument_registers().len());
        for slot in abi.argument_registers() {
            writer.u32(slot.index());
            writer.storage(slot.storage());
        }
        writer.usize(abi.return_registers().len());
        for slot in abi.return_registers() {
            writer.u32(slot.index());
            writer.storage(slot.storage());
        }
        writer.option_storage(abi.frame_pointer_storage());

        write_function_interface(&mut writer, self.function_interface.as_ref());

        let mut register_storages = self
            .register_storages_by_name
            .values()
            .copied()
            .collect::<Vec<_>>();
        register_storages.sort_unstable();
        register_storages.dedup();
        writer.usize(register_storages.len());
        for storage in register_storages {
            writer.storage(storage);
        }

        writer.usize(self.raw_call_sites_by_id.len());
        for (call_site, identity) in &self.raw_call_sites_by_id {
            writer.u32(call_site.0);
            write_call_identity(&mut writer, *identity);
        }
        writer.usize(self.call_site_interfaces.len());
        for interface in self.call_site_interfaces.values() {
            write_call_site_interface(&mut writer, interface);
        }

        writer.usize(self.memory_spaces_by_op.len());
        for ((block_addr, op_index), space) in &self.memory_spaces_by_op {
            writer.u64(*block_addr);
            writer.usize(*op_index);
            writer.space(*space);
        }
        writer.finish()
    }

    /// Rebind raw lifted memory-space identities to the completed SSA operation
    /// sites. SSA preparation may insert non-memory register-alias operations,
    /// but it must retain the order, count, and exact space identity of memory
    /// operations in each block. Any violation clears the map so certification
    /// fails closed.
    pub(crate) fn remap_memory_sites_to_prepared(&mut self, function: &SSAFunction) -> bool {
        let mut raw_by_block = BTreeMap::<u64, Vec<SpaceId>>::new();
        for ((block_addr, _), space) in &self.memory_spaces_by_op {
            raw_by_block.entry(*block_addr).or_default().push(*space);
        }

        let mut prepared_by_block = BTreeMap::<u64, Vec<(usize, SpaceId)>>::new();
        for block in function.blocks() {
            let sites = block
                .ops
                .iter()
                .enumerate()
                .filter_map(|(op_index, op)| ssa_memory_space(op).map(|space| (op_index, space)))
                .collect::<Vec<_>>();
            if !sites.is_empty() {
                prepared_by_block.insert(block.addr, sites);
            }
        }

        if raw_by_block.len() != prepared_by_block.len()
            || raw_by_block.iter().any(|(block_addr, raw)| {
                prepared_by_block.get(block_addr).is_none_or(|prepared| {
                    prepared.len() != raw.len()
                        || prepared
                            .iter()
                            .map(|(_, space)| *space)
                            .ne(raw.iter().copied())
                })
            })
        {
            self.memory_spaces_by_op.clear();
            return false;
        }

        let mut remapped = BTreeMap::new();
        for (block_addr, spaces) in raw_by_block {
            let Some(sites) = prepared_by_block.get(&block_addr) else {
                self.memory_spaces_by_op.clear();
                return false;
            };
            for ((op_index, space), _) in sites.iter().copied().zip(spaces) {
                remapped.insert((block_addr, op_index), space);
            }
        }
        self.memory_spaces_by_op = remapped;
        true
    }
}

#[cfg(test)]
fn is_memory_op(op: &SSAOp) -> bool {
    ssa_memory_space(op).is_some()
}

fn ssa_memory_space(op: &SSAOp) -> Option<SpaceId> {
    match op {
        SSAOp::Load { space, .. }
        | SSAOp::Store { space, .. }
        | SSAOp::LoadLinked { space, .. }
        | SSAOp::StoreConditional { space, .. }
        | SSAOp::AtomicCAS { space, .. }
        | SSAOp::LoadGuarded { space, .. }
        | SSAOp::StoreGuarded { space, .. } => Some(*space),
        _ => None,
    }
}

fn collect_raw_call_site_identities(
    blocks: &[R2ILBlock],
) -> BTreeMap<CallSiteId, SourceCallSiteIdentity> {
    let mut raw_calls = blocks
        .iter()
        .flat_map(|block| {
            block
                .ops
                .iter()
                .enumerate()
                .filter_map(move |(op_index, op)| match op {
                    R2ILOp::Call { target } => Some((
                        block.addr,
                        op_index,
                        Some(SourceCallSiteIdentity::new(
                            block.addr,
                            op_index,
                            CanonicalStorageId::from_varnode(target),
                        )),
                    )),
                    R2ILOp::CallInd { .. } => Some((block.addr, op_index, None)),
                    _ => None,
                })
        })
        .collect::<Vec<_>>();
    raw_calls.sort_unstable_by_key(|(block_addr, op_index, _)| (*block_addr, *op_index));
    raw_calls
        .into_iter()
        .enumerate()
        .filter_map(|(index, (_, _, identity))| {
            u32::try_from(index)
                .ok()
                .zip(identity)
                .map(|(index, identity)| (CallSiteId(index), identity))
        })
        .collect()
}

fn memory_space(op: &R2ILOp) -> Option<SpaceId> {
    match op {
        R2ILOp::Load { space, .. }
        | R2ILOp::Store { space, .. }
        | R2ILOp::LoadLinked { space, .. }
        | R2ILOp::StoreConditional { space, .. }
        | R2ILOp::AtomicCAS { space, .. }
        | R2ILOp::LoadGuarded { space, .. }
        | R2ILOp::StoreGuarded { space, .. } => Some(*space),
        _ => None,
    }
}

fn space_sort_key(space: SpaceId) -> (u8, u32) {
    match space {
        SpaceId::Ram => (0, 0),
        SpaceId::Register => (1, 0),
        SpaceId::Unique => (2, 0),
        SpaceId::Const => (3, 0),
        SpaceId::Custom(id) => (4, id),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{AddressSpace, RegisterDef, Varnode};

    fn register_storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn semantic_identity_arch(endianness: Endianness) -> ArchSpec {
        let mut arch = ArchSpec::new("semantic-identity-test");
        arch.addr_size = 8;
        arch.alignment = 1;
        arch.memory_endianness = endianness;
        arch.add_space(AddressSpace::ram(8));
        arch.add_register(RegisterDef::new("sp", 0, 8));
        arch.add_register(RegisterDef::new("ra", 8, 8));
        arch.add_register(RegisterDef::new("target", 16, 8));
        arch.add_register(RegisterDef::new("arg", 24, 8));
        arch
    }

    #[test]
    fn architecture_family_is_typed_schema_bound_semantic_identity() {
        let x86 = ArchSpec::new("x86:LE:64:default");
        let arm = ArchSpec::new("AARCH64:LE:64:v8A");
        let x86_context = SourceMachineContext::from_blocks(&[], Some(&x86));
        let arm_context = SourceMachineContext::from_blocks(&[], Some(&arm));

        assert_eq!(MACHINE_CONTEXT_SCHEMA_VERSION, 16);
        assert_eq!(x86_context.schema_version(), 16);
        assert_eq!(
            x86_context.architecture_family(),
            MachineArchitectureFamily::X86_64
        );
        assert_eq!(
            arm_context.architecture_family(),
            MachineArchitectureFamily::AArch64
        );
        assert_ne!(
            x86_context.semantic_identity_bytes(),
            arm_context.semantic_identity_bytes()
        );
    }

    #[test]
    fn machine_context_identity_binds_interfaces_calls_and_memory_geometry() {
        let little = semantic_identity_arch(Endianness::Little);
        let big = semantic_identity_arch(Endianness::Big);
        assert_ne!(
            SourceMachineContext::from_blocks(&[], Some(&little)).semantic_identity_bytes(),
            SourceMachineContext::from_blocks(&[], Some(&big)).semantic_identity_bytes(),
            "endianness is semantic identity"
        );

        let base_interface = SourceFunctionInterface::new_exact(
            b"machine-context-return-v1".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(register_storage(8, 8)))
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(0, 8)))
        .expect("exact base interface");
        let stacked_interface = base_interface
            .clone()
            .with_exact_stacked_return(0, 8, 8, 8)
            .expect("exact stacked return");
        let base = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&little),
            Some(base_interface),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        let stacked = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&little),
            Some(stacked_interface),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert_ne!(
            base.semantic_identity_bytes(),
            stacked.semantic_identity_bytes(),
            "return mechanics are semantic identity"
        );

        let target = Varnode::register(16, 8);
        let mut call_block = R2ILBlock::new(0x4000, 1);
        call_block.push(R2ILOp::Call { target });
        let identity = SourceCallSiteIdentity::new(0x4000, 0, register_storage(16, 8));
        let call_interface = |complete| {
            SourceCallSiteInterface::new(
                b"machine-context-call-v1".to_vec(),
                identity,
                complete,
                "test-abi",
                [SourceCallArgumentSpec::new(0, register_storage(24, 8))],
                false,
                false,
                SourceCallResult::Void,
            )
            .expect("exact call interface")
        };
        let incomplete = SourceMachineContext::from_blocks_with_interfaces(
            &[call_block.clone()],
            Some(&little),
            None,
            SourceMachineRoles::default(),
            None,
            vec![call_interface(false)],
        );
        let complete = SourceMachineContext::from_blocks_with_interfaces(
            &[call_block],
            Some(&little),
            None,
            SourceMachineRoles::default(),
            None,
            vec![call_interface(true)],
        );
        assert_ne!(
            incomplete.semantic_identity_bytes(),
            complete.semantic_identity_bytes(),
            "callsite completeness is semantic identity"
        );
    }

    #[test]
    fn function_interface_rejects_overlapping_parameter_aliases() {
        assert_eq!(
            SourceFunctionInterface::new(
                b"overlapping-register-interface".to_vec(),
                "test-abi",
                [
                    SourceAbiParameterSpec::new(0, register_storage(0, 8)),
                    SourceAbiParameterSpec::new(1, register_storage(4, 4)),
                ],
                SourceFunctionReturn::Void,
                [],
            ),
            Err(SourceFunctionInterfaceError::OverlappingRegisterStorages)
        );
    }

    #[test]
    fn exact_function_interface_retains_local_and_parameter_home_roles() {
        let parameter_storage = register_storage(0, 8);
        let base_storage = register_storage(64, 8);
        let interface = SourceFunctionInterface::new_exact(
            b"exact-stack-slot-roles".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, parameter_storage)],
            SourceFunctionReturn::Void,
            [
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    base_storage,
                    -16,
                    8,
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    base_storage,
                    -8,
                    8,
                    0,
                    parameter_storage,
                ),
            ],
        )
        .expect("classified stack-slot roles are exact");

        assert!(interface.stack_slot_roles_complete());
        assert_eq!(
            interface.stack_slots()[0].role(),
            SourceStackSlotRole::Local
        );
        assert_eq!(
            interface.stack_slots()[1].role(),
            SourceStackSlotRole::ParameterHome {
                parameter_index: 0,
                home_storage: parameter_storage,
            }
        );
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let artifact =
            crate::SsaArtifact::for_decompile_with_interface(&[block], None, interface.clone())
                .expect("SSA artifact retains the exact source interface");
        assert_eq!(
            artifact.machine_context().function_interface(),
            Some(&interface)
        );

        let compatibility = SourceFunctionInterface::new(
            b"compatibility-stack-slot".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, parameter_storage)],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new(
                StackAddressBase::FramePointer,
                base_storage,
                -8,
                8,
            )],
        )
        .expect("unclassified compatibility resource remains representable");
        assert!(!compatibility.stack_slot_roles_complete());
        assert_eq!(
            compatibility.stack_slots()[0].role(),
            SourceStackSlotRole::UnclassifiedResource
        );
    }

    #[test]
    fn stack_pointer_binding_is_explicit_disjoint_and_matches_stack_resources() {
        let parameter = register_storage(0, 8);
        let result = register_storage(8, 8);
        let stack_pointer = register_storage(64, 8);
        let frame_pointer = register_storage(72, 8);
        let return_address = register_storage(80, 8);
        let unbound = |slots| {
            SourceFunctionInterface::new_exact(
                b"typed-stack-pointer".to_vec(),
                "test-abi",
                [SourceAbiParameterSpec::new(0, parameter)],
                SourceFunctionReturn::Register { storage: result },
                slots,
            )
        };
        let build = |slots| {
            unbound(slots)
                .and_then(|interface| interface.with_return_address_storage(return_address))
        };

        assert_eq!(
            unbound(Vec::new())
                .and_then(|interface| interface.with_return_address_storage(parameter)),
            Err(SourceFunctionInterfaceError::InvalidReturnAddressStorage)
        );
        assert_eq!(
            unbound(Vec::new()).and_then(|interface| interface.with_return_address_storage(result)),
            Err(SourceFunctionInterfaceError::InvalidReturnAddressStorage)
        );
        assert_eq!(
            unbound(vec![SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                frame_pointer,
                -8,
                8,
            )])
            .and_then(|interface| interface.with_return_address_storage(frame_pointer)),
            Err(SourceFunctionInterfaceError::InvalidReturnAddressStorage)
        );
        assert_eq!(
            unbound(vec![SourceStackSlotSpec::new_local(
                StackAddressBase::StackPointer,
                stack_pointer,
                0,
                8,
            )])
            .and_then(|interface| interface.with_return_address_storage(stack_pointer)),
            Err(SourceFunctionInterfaceError::InvalidReturnAddressStorage)
        );

        let slotless = build(Vec::new())
            .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
            .expect("slotless interfaces still carry exit machine state");
        assert_eq!(slotless.stack_pointer_storage(), Some(stack_pointer));

        let frame_only = build(vec![SourceStackSlotSpec::new_local(
            StackAddressBase::FramePointer,
            frame_pointer,
            -8,
            8,
        )])
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("frame-pointer resources are disjoint from the stack pointer");
        assert_eq!(frame_only.stack_pointer_storage(), Some(stack_pointer));

        let mixed = build(vec![
            SourceStackSlotSpec::new_local(StackAddressBase::FramePointer, frame_pointer, -8, 8),
            SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, stack_pointer, 0, 8),
        ])
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("mixed bases retain the exact stack-pointer carrier");
        assert_eq!(mixed.stack_pointer_storage(), Some(stack_pointer));

        assert_eq!(
            build(vec![SourceStackSlotSpec::new_local(
                StackAddressBase::StackPointer,
                stack_pointer,
                0,
                8,
            )])
            .and_then(|interface| {
                interface.with_stack_pointer_storage(register_storage(88, 8))
            }),
            Err(SourceFunctionInterfaceError::InvalidStackPointerStorage)
        );
        assert_eq!(
            build(Vec::new()).and_then(|interface| interface.with_stack_pointer_storage(parameter)),
            Err(SourceFunctionInterfaceError::InvalidStackPointerStorage)
        );
        assert_eq!(
            build(vec![SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                frame_pointer,
                -8,
                8,
            )])
            .and_then(|interface| interface.with_stack_pointer_storage(frame_pointer)),
            Err(SourceFunctionInterfaceError::InvalidStackPointerStorage)
        );
    }

    #[test]
    fn exact_machine_interface_requires_declared_full_width_ra_and_sp() {
        let stack_pointer = register_storage(64, 8);
        let return_address = register_storage(80, 8);
        let make = || {
            SourceFunctionInterface::new_exact(
                b"exact-machine-roles".to_vec(),
                "test-abi",
                [],
                SourceFunctionReturn::Void,
                [],
            )
            .expect("exact interface")
        };
        let mut arch = ArchSpec::new("exact-machine-roles");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("sp", stack_pointer.offset, 8));
        arch.add_register(RegisterDef::new("lr", return_address.offset, 8));

        let without_roles = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(make()),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(!without_roles.abi_model().is_coherent());

        let return_only = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(
                make()
                    .with_return_address_storage(return_address)
                    .expect("return-address role"),
            ),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(!return_only.abi_model().is_coherent());

        let complete = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(
                make()
                    .with_return_address_storage(return_address)
                    .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
                    .expect("exact machine roles"),
            ),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(complete.abi_model().is_coherent());

        let compatibility = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(
                SourceFunctionInterface::new(
                    b"compatibility-machine-roles".to_vec(),
                    "test-abi",
                    [],
                    SourceFunctionReturn::Void,
                    [],
                )
                .and_then(|interface| interface.with_return_address_storage(return_address))
                .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
                .expect("compatibility interface remains representable for refusal diagnostics"),
            ),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(
            !compatibility.abi_model().is_coherent(),
            "legacy incomplete-role interfaces must never supply usable ABI authority"
        );

        let narrow_stack_pointer = register_storage(96, 4);
        arch.add_register(RegisterDef::new("narrow_sp", 96, 4));
        let narrow = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(
                make()
                    .with_return_address_storage(return_address)
                    .and_then(|interface| {
                        interface.with_stack_pointer_storage(narrow_stack_pointer)
                    })
                    .expect("standalone binding is architecture-independent"),
            ),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(!narrow.abi_model().is_coherent());

        let subregister_stack_pointer = register_storage(104, 8);
        arch.add_register(RegisterDef::sub("sp_alias", 104, 8, "missing_sp_parent"));
        let subregister_sp = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(
                make()
                    .with_return_address_storage(return_address)
                    .and_then(|interface| {
                        interface.with_stack_pointer_storage(subregister_stack_pointer)
                    })
                    .expect("standalone binding cannot inspect ArchSpec parentage"),
            ),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(!subregister_sp.abi_model().is_coherent());

        let subregister_return_address = register_storage(112, 8);
        arch.add_register(RegisterDef::sub("lr_alias", 112, 8, "missing_lr_parent"));
        let subregister_ra = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(
                make()
                    .with_return_address_storage(subregister_return_address)
                    .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
                    .expect("standalone binding cannot inspect ArchSpec parentage"),
            ),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(!subregister_ra.abi_model().is_coherent());
    }

    #[test]
    fn exact_stacked_return_requires_matching_registers_and_byte_ram() {
        let stack_pointer = register_storage(64, 8);
        let return_address = register_storage(80, 8);
        let make = || {
            SourceFunctionInterface::new_exact(
                b"exact-stacked-return".to_vec(),
                "test-abi",
                [],
                SourceFunctionReturn::Void,
                [],
            )
            .and_then(|interface| interface.with_return_address_storage(return_address))
            .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
            .expect("exact machine roles")
        };
        let exact = make()
            .with_exact_stacked_return(0, 8, 8, 8)
            .expect("canonical stacked return");
        let mut arch = ArchSpec::new("exact-stacked-return");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("source-ra", return_address.offset, 8));
        arch.add_register(RegisterDef::new("source-sp", stack_pointer.offset, 8));
        arch.add_space(AddressSpace::ram(8));

        let coherent = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(exact.clone()),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(coherent.abi_model().is_coherent());
        assert_eq!(coherent.return_mechanism(), exact.return_mechanism());

        let absent = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(make()),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(absent.abi_model().is_coherent());
        assert_eq!(absent.return_mechanism(), None);

        let mut subregister = arch.clone();
        subregister.registers.clear();
        subregister.add_register(RegisterDef::sub(
            "source-ra-alias",
            return_address.offset,
            8,
            "untrusted-parent",
        ));
        subregister.add_register(RegisterDef::new("source-sp", stack_pointer.offset, 8));
        let context = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&subregister),
            Some(exact.clone()),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(!context.abi_model().is_coherent());

        let mut wrong_machine_width = arch.clone();
        wrong_machine_width.addr_size = 4;
        wrong_machine_width.spaces.clear();
        wrong_machine_width.add_space(AddressSpace::ram(4));
        let context = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&wrong_machine_width),
            Some(exact.clone()),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(!context.abi_model().is_coherent());

        let mut word_addressed = arch.clone();
        word_addressed.spaces[0].word_size = 2;
        let context = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&word_addressed),
            Some(exact.clone()),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(!context.abi_model().is_coherent());

        let mut wrong_ram_width = arch;
        wrong_ram_width.spaces[0].addr_size = 4;
        let context = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&wrong_ram_width),
            Some(exact),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(!context.abi_model().is_coherent());
    }

    #[test]
    fn exact_machine_interface_requires_top_level_address_width_frame_pointer() {
        let stack_pointer = register_storage(64, 8);
        let frame_pointer = register_storage(72, 8);
        let return_address = register_storage(80, 8);
        let make_explicit = |frame_pointer| {
            SourceFunctionInterface::new_exact(
                b"exact-machine-frame-pointer".to_vec(),
                "test-abi",
                [],
                SourceFunctionReturn::Void,
                [],
            )
            .and_then(|interface| interface.with_return_address_storage(return_address))
            .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
            .and_then(|interface| interface.with_frame_pointer_storage(frame_pointer))
            .expect("exact disjoint frame carriers")
        };
        let make_slot_derived = |frame_pointer, stack_pointer, return_address| {
            SourceFunctionInterface::new_exact(
                b"slot-derived-machine-frame-pointer".to_vec(),
                "test-abi",
                [],
                SourceFunctionReturn::Void,
                [SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    frame_pointer,
                    -8,
                    8,
                )],
            )
            .and_then(|interface| interface.with_return_address_storage(return_address))
            .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
            .expect("exact slot-derived frame carriers")
        };
        let mut arch = ArchSpec::new("exact-machine-frame-pointer");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("sp", stack_pointer.offset, 8));
        arch.add_register(RegisterDef::new("fp", frame_pointer.offset, 8));
        arch.add_register(RegisterDef::new("lr", return_address.offset, 8));

        let coherent = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(make_explicit(frame_pointer)),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(coherent.abi_model().is_coherent());
        assert_eq!(
            coherent.abi_model().frame_pointer_storage(),
            Some(frame_pointer)
        );

        let slot_derived = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(make_slot_derived(
                frame_pointer,
                stack_pointer,
                return_address,
            )),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(slot_derived.abi_model().is_coherent());
        assert_eq!(
            slot_derived.abi_model().frame_pointer_storage(),
            Some(frame_pointer)
        );

        let absent = SourceFunctionInterface::new_exact(
            b"absent-machine-frame-pointer".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(return_address))
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("frame-pointer absence remains representable");
        let absent = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(absent),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(absent.abi_model().is_coherent());
        assert_eq!(absent.abi_model().frame_pointer_storage(), None);

        let narrow_stack_pointer = register_storage(88, 4);
        let narrow_frame_pointer = register_storage(92, 4);
        let narrow_return_address = register_storage(96, 4);
        arch.add_register(RegisterDef::new(
            "narrow_fp",
            narrow_frame_pointer.offset,
            narrow_frame_pointer.size,
        ));
        arch.add_register(RegisterDef::new(
            "narrow_sp",
            narrow_stack_pointer.offset,
            narrow_stack_pointer.size,
        ));
        arch.add_register(RegisterDef::new(
            "narrow_lr",
            narrow_return_address.offset,
            narrow_return_address.size,
        ));
        let narrow_interface = SourceFunctionInterface::new_exact(
            b"narrow-machine-frame-pointer".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                narrow_frame_pointer,
                -8,
                4,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(narrow_return_address))
        .and_then(|interface| interface.with_stack_pointer_storage(narrow_stack_pointer))
        .expect("source-width-coherent narrow carriers remain representable");
        let narrow = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(narrow_interface),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(!narrow.abi_model().is_coherent());

        let subregister_frame_pointer = register_storage(104, 8);
        arch.add_register(RegisterDef::sub(
            "fp_alias",
            subregister_frame_pointer.offset,
            subregister_frame_pointer.size,
            "missing_fp_parent",
        ));
        let subregister = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(make_slot_derived(
                subregister_frame_pointer,
                stack_pointer,
                return_address,
            )),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(!subregister.abi_model().is_coherent());

        assert!(!is_exact_top_level_address_register(
            &arch,
            CanonicalStorageId {
                space: CanonicalStorageSpace::Ram,
                offset: frame_pointer.offset,
                size: frame_pointer.size,
            },
            8,
        ));

        let overlapping = SourceFunctionInterface::new_exact(
            b"overlapping-machine-frame-pointer".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, frame_pointer)],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                frame_pointer,
                -8,
                8,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(return_address))
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("representable overlapping source carrier");
        let overlapping = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(overlapping),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(!overlapping.abi_model().is_coherent());
    }

    #[test]
    fn exact_function_interface_rejects_malformed_parameter_homes() {
        let parameter_storage = register_storage(0, 8);
        let base_storage = register_storage(64, 8);
        let build = |slots| {
            SourceFunctionInterface::new_exact(
                b"malformed-stack-slot-role".to_vec(),
                "test-abi",
                [SourceAbiParameterSpec::new(0, parameter_storage)],
                SourceFunctionReturn::Void,
                slots,
            )
        };

        assert_eq!(
            build(vec![SourceStackSlotSpec::new(
                StackAddressBase::FramePointer,
                base_storage,
                -8,
                8,
            )]),
            Err(SourceFunctionInterfaceError::InvalidStackSlotRole)
        );
        assert_eq!(
            build(vec![SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::FramePointer,
                base_storage,
                -8,
                8,
                1,
                parameter_storage,
            )]),
            Err(SourceFunctionInterfaceError::InvalidStackSlotRole)
        );
        assert_eq!(
            build(vec![SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::FramePointer,
                base_storage,
                -8,
                8,
                0,
                register_storage(8, 8),
            )]),
            Err(SourceFunctionInterfaceError::InvalidStackSlotRole)
        );
        assert_eq!(
            build(vec![
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    base_storage,
                    -8,
                    8,
                    0,
                    parameter_storage,
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::StackPointer,
                    register_storage(72, 8),
                    -8,
                    8,
                    0,
                    parameter_storage,
                ),
            ]),
            Err(SourceFunctionInterfaceError::InvalidStackSlotRole)
        );
    }

    fn demo_struct_type_graph() -> SourceTypeGraph {
        let members = (0..14).map(|index| {
            SourceAggregateMember::new(
                index,
                1,
                u64::from(index) * 32,
                32,
                format!("member_{index}"),
            )
        });
        SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::Struct { aggregate_id: 0 }, 56 * 8, 32),
                SourceType::new(1, SourceTypeKind::SignedInteger, 32, 32),
                SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
            ],
            [SourceAggregateLayout::new(
                0,
                0,
                56 * 8,
                32,
                "DemoStruct",
                members,
            )],
        )
        .expect("valid exact DemoStruct graph")
    }

    #[test]
    fn function_interface_retains_exact_logical_type_graph() {
        assert_eq!(
            SourceTypeGraph::new(
                [SourceType::new(0, SourceTypeKind::SignedInteger, 32, 16)],
                [],
            ),
            Err(SourceTypeGraphError::InvalidType)
        );
        let pointer32 = SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::Struct { aggregate_id: 0 }, 32, 32),
                SourceType::new(1, SourceTypeKind::SignedInteger, 32, 32),
                SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 0 }, 32, 32),
            ],
            [SourceAggregateLayout::new(
                0,
                0,
                32,
                32,
                "OneField",
                [SourceAggregateMember::new(0, 1, 0, 32, "value")],
            )],
        )
        .expect("valid 32-bit pointer graph");
        assert!(pointer32.validates_pointer_width(32));
        assert!(!pointer32.validates_pointer_width(64));
        let parameters = [
            SourceAbiParameterSpec::new(0, register_storage(0, 8)),
            SourceAbiParameterSpec::new(1, register_storage(8, 8)),
            SourceAbiParameterSpec::new(2, register_storage(16, 8)),
        ];
        let low_i32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        let interface = SourceFunctionInterface::new_with_logical_types(
            b"exact-type-layout".to_vec(),
            "test-abi",
            parameters,
            SourceFunctionReturn::Register {
                storage: register_storage(24, 8),
            },
            [],
            [
                SourceLogicalValue::new(
                    2,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(1, low_i32),
                SourceLogicalValue::new(1, low_i32),
            ],
            Some(SourceLogicalValue::new(1, low_i32)),
            Some(demo_struct_type_graph()),
        )
        .expect("valid exact logical interface");

        assert_eq!(
            interface.schema_version(),
            SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        );
        assert_eq!(interface.parameter_logical_values()[0].type_id(), 2);
        assert_eq!(
            interface.parameter_logical_values()[1].carrier().kind(),
            SourceCarrierKind::LowBits
        );
        let graph = interface.type_graph().expect("retained exact graph");
        assert_eq!(graph.schema_version(), SOURCE_TYPE_GRAPH_SCHEMA_VERSION);
        assert_eq!(graph.types().len(), 3);
        assert_eq!(graph.aggregates()[0].name(), "DemoStruct");
        assert_eq!(graph.aggregates()[0].members()[2].offset_bits(), 8 * 8);
        assert_eq!(graph.aggregates()[0].members()[13].offset_bits(), 52 * 8);

        let invalid = SourceFunctionInterface::new_with_logical_types(
            b"exact-type-layout".to_vec(),
            "test-abi",
            parameters,
            SourceFunctionReturn::Register {
                storage: register_storage(24, 8),
            },
            [],
            [
                SourceLogicalValue::new(
                    2,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(
                    1,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 32),
                ),
                SourceLogicalValue::new(1, low_i32),
            ],
            Some(SourceLogicalValue::new(1, low_i32)),
            Some(demo_struct_type_graph()),
        );
        assert_eq!(
            invalid,
            Err(SourceFunctionInterfaceError::InvalidLogicalTypes)
        );
    }

    #[test]
    fn function_interface_accepts_exact_unsigned_byte_pointee() {
        let graph = SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::UnsignedInteger, 8, 8),
                SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
                SourceType::new(2, SourceTypeKind::UnsignedInteger, 64, 64),
            ],
            [],
        )
        .expect("unsigned-byte pointer graph");
        let full64 = SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64);
        let interface = SourceFunctionInterface::new_exact_with_logical_types(
            b"fnv-u8-pointer-revision".to_vec(),
            "aapcs64",
            [
                SourceAbiParameterSpec::new(0, register_storage(0, 8)),
                SourceAbiParameterSpec::new(1, register_storage(8, 8)),
            ],
            SourceFunctionReturn::Register {
                storage: register_storage(0, 8),
            },
            [],
            [
                SourceLogicalValue::new(1, full64),
                SourceLogicalValue::new(2, full64),
            ],
            Some(SourceLogicalValue::new(2, full64)),
            Some(graph),
        )
        .expect("exact FNV logical interface");

        let graph = interface.type_graph().expect("logical graph");
        assert_eq!(
            graph.types()[1].kind(),
            SourceTypeKind::Pointer { target_type_id: 0 }
        );
        assert_eq!(graph.types()[0].kind(), SourceTypeKind::UnsignedInteger);
    }

    #[test]
    fn source_type_graph_accepts_pointer_to_pointer() {
        let graph = SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::SignedInteger, 8, 8),
                SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
                SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 1 }, 64, 64),
            ],
            [],
        )
        .expect("char ** is a well formed source type");
        assert_eq!(
            graph.types()[2].kind(),
            SourceTypeKind::Pointer { target_type_id: 1 }
        );
        assert!(graph.validates_pointer_width(64));
    }

    #[test]
    fn source_type_graph_rejects_pointer_to_absent_target() {
        assert_eq!(
            SourceTypeGraph::new(
                [SourceType::new(
                    0,
                    SourceTypeKind::Pointer { target_type_id: 1 },
                    64,
                    64,
                )],
                [],
            ),
            Err(SourceTypeGraphError::InvalidType)
        );
    }

    #[test]
    fn callsite_interface_rejects_bad_order_overlap_and_noreturn_result() {
        let identity = SourceCallSiteIdentity::new(
            0x1000,
            0,
            CanonicalStorageId {
                space: CanonicalStorageSpace::Ram,
                offset: 0x2000,
                size: 8,
            },
        );
        assert_eq!(
            SourceCallSiteInterface::new(
                b"call-revision".to_vec(),
                identity,
                true,
                "test-abi",
                [SourceCallArgumentSpec::new(1, register_storage(0, 8))],
                false,
                false,
                SourceCallResult::Void,
            ),
            Err(SourceCallSiteInterfaceError::InvalidArgumentOrder)
        );
        assert_eq!(
            SourceCallSiteInterface::new(
                b"call-revision".to_vec(),
                identity,
                true,
                "test-abi",
                [
                    SourceCallArgumentSpec::new(0, register_storage(0, 8)),
                    SourceCallArgumentSpec::new(1, register_storage(4, 8)),
                ],
                false,
                false,
                SourceCallResult::Void,
            ),
            Err(SourceCallSiteInterfaceError::OverlappingRegisterStorages)
        );
        assert_eq!(
            SourceCallSiteInterface::new(
                b"call-revision".to_vec(),
                identity,
                true,
                "test-abi",
                [],
                false,
                true,
                SourceCallResult::Register {
                    storage: register_storage(0, 8),
                },
            ),
            Err(SourceCallSiteInterfaceError::NoreturnWithResult)
        );
    }

    #[test]
    fn raw_direct_callsite_ids_are_sorted_and_retain_exact_targets() {
        let low_target = Varnode::ram(0x3000, 8);
        let high_target = Varnode::ram(0x4000, 8);
        let mut high = R2ILBlock::new(0x2000, 4);
        high.push(R2ILOp::Call {
            target: high_target.clone(),
        });
        let mut low = R2ILBlock::new(0x1000, 4);
        low.push(R2ILOp::Call {
            target: low_target.clone(),
        });

        let context = SourceMachineContext::from_blocks(&[high, low], None);
        assert_eq!(
            context.raw_call_site_identity(CallSiteId(0)),
            Some(SourceCallSiteIdentity::new(
                0x1000,
                0,
                CanonicalStorageId::from_varnode(&low_target),
            ))
        );
        assert_eq!(
            context.raw_call_site_identity(CallSiteId(1)),
            Some(SourceCallSiteIdentity::new(
                0x2000,
                0,
                CanonicalStorageId::from_varnode(&high_target),
            ))
        );
    }

    #[test]
    fn prepared_memory_sites_follow_inserted_register_alias_operations() {
        let mut arch = ArchSpec::new("prepared-memory-site-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rdi", 0, 8));
        arch.add_register(RegisterDef::new("edi", 0, 4));
        arch.add_register(RegisterDef::new("rax", 8, 8));
        arch.add_register(RegisterDef::new("eax", 8, 4));

        let mut block = R2ILBlock::new(0x2400, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::register(0, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x100, 4),
            space: SpaceId::Custom(7),
            addr: Varnode::register(8, 4),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(8, 8),
        });

        let function = SSAFunction::from_blocks_for_decompile(&[block.clone()], Some(&arch))
            .expect("prepared SSA");
        let prepared_index = function
            .get_block(0x2400)
            .expect("prepared block")
            .ops
            .iter()
            .position(is_memory_op)
            .expect("prepared memory operation");
        assert!(prepared_index > 1, "alias extraction must precede the load");

        let mut context = SourceMachineContext::from_blocks(&[block], Some(&arch));
        assert_eq!(context.memory_space_at(0x2400, 1), Some(SpaceId::Custom(7)));
        assert!(context.remap_memory_sites_to_prepared(&function));
        assert_eq!(
            context.memory_space_at(0x2400, prepared_index),
            Some(SpaceId::Custom(7))
        );
        assert_eq!(context.memory_spaces_by_op().len(), 1);
    }

    #[test]
    fn prepared_memory_sites_reject_swapped_space_identities() {
        let mut block = R2ILBlock::new(0x2500, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x100, 4),
            space: SpaceId::Ram,
            addr: Varnode::register(0, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Custom(7),
            addr: Varnode::register(8, 8),
            val: Varnode::unique(0x100, 4),
        });

        let mut function =
            SSAFunction::from_blocks_raw(&[block.clone()], None).expect("raw SSA function");
        let prepared = &mut function.get_block_mut(0x2500).expect("prepared block").ops;
        match &mut prepared[0] {
            SSAOp::Load { space, .. } => *space = SpaceId::Custom(7),
            op => panic!("expected load, got {op:?}"),
        }
        match &mut prepared[1] {
            SSAOp::Store { space, .. } => *space = SpaceId::Ram,
            op => panic!("expected store, got {op:?}"),
        }

        let mut context = SourceMachineContext::from_blocks(&[block], None);
        assert!(!context.remap_memory_sites_to_prepared(&function));
        assert!(context.memory_spaces_by_op().is_empty());
    }

    #[test]
    fn interface_registers_missing_from_architecture_are_incoherent() {
        let interface = SourceFunctionInterface::new(
            b"missing-register-interface".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, register_storage(0, 8))],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("valid standalone interface");
        let context = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            None,
            Some(interface),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(context.abi_model().is_available());
        assert!(!context.abi_model().is_coherent());
    }

    #[test]
    fn stack_base_storage_missing_from_architecture_is_incoherent() {
        let interface = SourceFunctionInterface::new(
            b"missing-stack-base-interface".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new(
                StackAddressBase::StackPointer,
                register_storage(52, 4),
                -16,
                4,
            )],
        )
        .expect("valid standalone stack interface");
        let mut arch = ArchSpec::new("stack-base-mismatch-test");
        arch.addr_size = 4;
        arch.add_register(RegisterDef::new("r0", 0, 4));
        let context = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(interface),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );

        assert!(context.abi_model().is_available());
        assert!(!context.abi_model().is_coherent());
    }

    #[test]
    fn missing_architecture_keeps_typed_sites_but_marks_model_unavailable() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x10, 4),
            space: SpaceId::Custom(7),
            addr: Varnode::register(0, 8),
        });
        let context = SourceMachineContext::from_blocks(&[block], None);

        assert!(!context.memory_model().is_available());
        assert!(!context.memory_model().is_coherent());
        assert_eq!(context.memory_space_at(0x1000, 0), Some(SpaceId::Custom(7)));
    }

    #[test]
    fn architecture_snapshot_applies_per_space_endianness() {
        let mut arch = ArchSpec::new("test-be");
        arch.addr_size = 8;
        arch.alignment = 4;
        arch.set_memory_endianness(Endianness::Big);
        let mut custom = AddressSpace::new(SpaceId::Custom(3), "little-data", 4);
        custom.word_size = 2;
        custom.endianness = Some(Endianness::Little);
        arch.add_space(custom);
        let context = SourceMachineContext::from_blocks(&[], Some(&arch));
        let model = context.memory_model();

        assert!(model.is_available());
        assert!(model.is_coherent());
        assert_eq!(model.default_address_bits(), 64);
        assert_eq!(model.default_endianness(), MachineMemoryEndianness::Big);
        assert_eq!(
            model
                .space(SpaceId::Ram)
                .map(MachineMemorySpace::endianness),
            Some(MachineMemoryEndianness::Big)
        );
        let custom = model.space(SpaceId::Custom(3)).expect("custom space");
        assert_eq!(custom.address_bits(), 32);
        assert_eq!(custom.word_size_bytes(), 2);
        assert_eq!(custom.endianness(), MachineMemoryEndianness::Little);
    }

    #[test]
    fn architecture_snapshot_uses_r2il_effective_address_size_fallback() {
        let mut arch = ArchSpec::new("fallback-address-size");
        arch.addr_size = 1;
        arch.add_register(RegisterDef::new("pc", 0, 8));
        arch.add_space(AddressSpace::new(SpaceId::Custom(9), "fallback", 1));
        let context = SourceMachineContext::from_blocks(&[], Some(&arch));
        let model = context.memory_model();

        assert_eq!(model.default_address_bits(), 64);
        assert_eq!(
            model
                .space(SpaceId::Custom(9))
                .map(MachineMemorySpace::address_bits),
            Some(64)
        );
        assert_eq!(
            model
                .space(SpaceId::Ram)
                .map(MachineMemorySpace::address_bits),
            Some(64)
        );
    }
}
