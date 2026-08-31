//! Serialization support for r2il types.
//!
//! This module provides binary serialization using postcard for efficient
//! storage and loading of architecture specifications.

use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::mem::size_of;
use std::path::Path;
use thiserror::Error;

use crate::opcode::R2ILOp;
use crate::space::AddressSpace;
use crate::{Endianness, MAGIC};

/// Errors that can occur during serialization/deserialization.
#[derive(Debug, Error)]
pub enum SerializeError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Serialization error: {0}")]
    Postcard(#[from] postcard::Error),

    #[error("Invalid architecture specification: {0}")]
    Validation(#[from] crate::ValidationError),

    #[error("Invalid format discriminator: expected R2PSTC07")]
    InvalidMagic,

    #[error("Truncated r2il representation")]
    Truncated,

    #[error("Trailing bytes after the r2il payload: {0}")]
    TrailingBytes(usize),

    #[error("R2IL payload is too large for this platform: {0} bytes")]
    PayloadTooLarge(u64),
}

/// Result type for serialization operations.
pub type Result<T> = std::result::Result<T, SerializeError>;

/// Definition of a processor register.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegisterDef {
    /// Register name (e.g., "RAX", "EAX", "AX", "AL")
    pub name: String,
    /// Offset in register space
    pub offset: u64,
    /// Size in bytes
    pub size: u32,
    /// Parent register name (if this is a sub-register)
    pub parent: Option<String>,
}

impl RegisterDef {
    /// Create a new register definition.
    pub fn new(name: impl Into<String>, offset: u64, size: u32) -> Self {
        Self {
            name: name.into(),
            offset,
            size,
            parent: None,
        }
    }

    /// Create a sub-register definition.
    pub fn sub(name: impl Into<String>, offset: u64, size: u32, parent: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            offset,
            size,
            parent: Some(parent.into()),
        }
    }

    /// Return the name-free storage occupied by this register declaration.
    pub const fn storage(&self) -> RegisterStorage {
        RegisterStorage {
            offset: self.offset,
            size: self.size,
        }
    }
}

/// One byte range in the architecture's register address space.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct RegisterStorage {
    /// Byte offset in register space.
    pub offset: u64,
    /// Width in bytes.
    pub size: u32,
}

impl RegisterStorage {
    /// Return the exclusive byte end, or `None` when the range is invalid.
    pub fn checked_end(self) -> Option<u64> {
        (self.size != 0)
            .then(|| self.offset.checked_add(u64::from(self.size)))
            .flatten()
    }

    /// Whether this valid storage completely contains another valid storage.
    pub fn contains(self, other: Self) -> bool {
        self.offset <= other.offset
            && self
                .checked_end()
                .zip(other.checked_end())
                .is_some_and(|(carrier_end, written_end)| written_end <= carrier_end)
    }
}

/// The exact bit range a register access occupies in its canonical carrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct RegisterBitSlice {
    /// Least-significant bit offset in the carrier.
    pub lsb_bit_offset: u64,
    /// Width in bits.
    pub size_bits: u64,
}

/// Why source-owned register geometry could not certify a projection.
///
/// These are geometry failures only. Architectural write effects are properties
/// of lifted definitions and deliberately do not appear in this contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum RegisterProjectionRefusal {
    /// A declared byte range is empty or its exclusive end overflows.
    InvalidStorageRange,
    /// No declared carrier contains this storage.
    NoContainingCarrier,
    /// More than one incomparable carrier could own this storage.
    AmbiguousContainingCarrier,
    /// Two declarations for one storage supplied incompatible geometry.
    ConflictingDeclarations,
    /// Declared register ranges overlap without either containing the other.
    PartialOverlap,
    /// The source did not provide the byte significance needed for a bit slice.
    MissingRegisterEndianness,
}

/// Either an exact carrier projection or a typed geometry refusal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum RegisterProjectionDisposition {
    /// Exact source-owned carrier and bit slice.
    Bound {
        carrier: RegisterStorage,
        slice: RegisterBitSlice,
    },
    /// Geometry was present but could not be certified.
    Refused { reason: RegisterProjectionRefusal },
}

/// Canonical projection for one unique declared register storage.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct RegisterProjection {
    /// The accessed register storage this entry describes.
    pub written: RegisterStorage,
    /// Its certified carrier geometry or explicit refusal.
    pub disposition: RegisterProjectionDisposition,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RegisterByteOrder {
    Little,
    Big,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RegisterProjectionComponentDisposition {
    Bound {
        carrier: RegisterStorage,
        byte_order: Option<RegisterByteOrder>,
    },
    Refused {
        reason: RegisterProjectionRefusal,
    },
}

/// One validated register component used to project observed, unnamed slices.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RegisterProjectionComponent {
    start: u64,
    end: u64,
    disposition: RegisterProjectionComponentDisposition,
}

/// Canonical query over one validated source-owned register geometry table.
///
/// Architecture tables contain one entry per declared register. Lifted P-code
/// may additionally address an unnamed lane inside a declared carrier. This
/// query derives that lane from the same validated laminar component and the
/// source register-space byte order (or, when legacy hand-built specs omit it,
/// the declared slices' unique orientation). Consumers do not repeat
/// containment or endian policy.
/// Construction is one `O(n log n)` pass. Exact declared lookups and component
/// lookups are `O(log n)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegisterProjectionQuery {
    exact: Vec<RegisterProjection>,
    components: Vec<RegisterProjectionComponent>,
}

impl RegisterProjectionQuery {
    /// Build the canonical query, or return `None` when source geometry is
    /// explicitly unavailable.
    pub fn from_arch(arch: &ArchSpec) -> std::result::Result<Option<Self>, crate::ValidationError> {
        crate::validate_register_geometry(arch)?;
        if arch.register_projections.is_empty() {
            return Ok(None);
        }

        let mut ordered = arch.register_projections.iter().collect::<Vec<_>>();
        ordered.sort_by(|left, right| {
            let left_end = left
                .written
                .checked_end()
                .expect("validated register storage");
            let right_end = right
                .written
                .checked_end()
                .expect("validated register storage");
            left.written
                .offset
                .cmp(&right.written.offset)
                .then_with(|| right_end.cmp(&left_end))
                .then_with(|| left.written.cmp(&right.written))
        });

        let register_byte_order = source_register_byte_order(arch);

        let mut components = Vec::new();
        let mut start = 0;
        while start < ordered.len() {
            let component_start = ordered[start].written.offset;
            let mut component_end = ordered[start]
                .written
                .checked_end()
                .expect("validated register storage");
            let mut limit = start + 1;
            while limit < ordered.len() && ordered[limit].written.offset < component_end {
                component_end = component_end.max(
                    ordered[limit]
                        .written
                        .checked_end()
                        .expect("validated register storage"),
                );
                limit += 1;
            }
            let members = &ordered[start..limit];
            let disposition = projection_component_disposition(members, register_byte_order);
            components.push(RegisterProjectionComponent {
                start: component_start,
                end: component_end,
                disposition,
            });
            start = limit;
        }

        Ok(Some(Self {
            exact: arch.register_projections.clone(),
            components,
        }))
    }

    /// Project one observed register-space range through its unique validated
    /// carrier. The returned entry always names the queried `written` range.
    pub fn project(&self, written: RegisterStorage) -> RegisterProjection {
        let refused = |reason| RegisterProjection {
            written,
            disposition: RegisterProjectionDisposition::Refused { reason },
        };
        let Some(written_end) = written.checked_end() else {
            return refused(RegisterProjectionRefusal::InvalidStorageRange);
        };
        if let Ok(index) = self
            .exact
            .binary_search_by_key(&written, |projection| projection.written)
        {
            return self.exact[index];
        }

        let insertion = self
            .components
            .partition_point(|component| component.start <= written.offset);
        let Some(component) = insertion
            .checked_sub(1)
            .and_then(|index| self.components.get(index))
        else {
            return refused(RegisterProjectionRefusal::NoContainingCarrier);
        };
        if written_end > component.end {
            return refused(RegisterProjectionRefusal::NoContainingCarrier);
        }

        let RegisterProjectionComponentDisposition::Bound {
            carrier,
            byte_order,
        } = component.disposition
        else {
            let RegisterProjectionComponentDisposition::Refused { reason } = component.disposition
            else {
                unreachable!("component disposition is exhaustive")
            };
            return refused(reason);
        };
        if !carrier.contains(written) {
            return refused(RegisterProjectionRefusal::NoContainingCarrier);
        }
        let Some(byte_order) = byte_order else {
            return refused(RegisterProjectionRefusal::MissingRegisterEndianness);
        };
        let carrier_end = carrier
            .checked_end()
            .expect("validated carrier storage has an end");
        let byte_offset = match byte_order {
            RegisterByteOrder::Little => written.offset.checked_sub(carrier.offset),
            RegisterByteOrder::Big => carrier_end.checked_sub(written_end),
        };
        let Some(lsb_bit_offset) = byte_offset.and_then(|offset| offset.checked_mul(8)) else {
            return refused(RegisterProjectionRefusal::InvalidStorageRange);
        };
        RegisterProjection {
            written,
            disposition: RegisterProjectionDisposition::Bound {
                carrier,
                slice: RegisterBitSlice {
                    lsb_bit_offset,
                    size_bits: u64::from(written.size) * 8,
                },
            },
        }
    }
}

fn source_register_byte_order(
    arch: &ArchSpec,
) -> std::result::Result<Option<RegisterByteOrder>, RegisterProjectionRefusal> {
    let mut byte_order = None;
    for space in arch
        .spaces
        .iter()
        .filter(|space| space.id == crate::SpaceId::Register)
    {
        let declared = match space.endianness {
            Some(Endianness::Little) => RegisterByteOrder::Little,
            Some(Endianness::Big) => RegisterByteOrder::Big,
            Some(Endianness::Mixed | Endianness::Custom) => {
                return Err(RegisterProjectionRefusal::MissingRegisterEndianness);
            }
            None => continue,
        };
        match byte_order {
            Some(existing) if existing != declared => {
                return Err(RegisterProjectionRefusal::ConflictingDeclarations);
            }
            Some(_) => {}
            None => byte_order = Some(declared),
        }
    }
    Ok(byte_order)
}

fn projection_component_disposition(
    members: &[&RegisterProjection],
    source_byte_order: std::result::Result<Option<RegisterByteOrder>, RegisterProjectionRefusal>,
) -> RegisterProjectionComponentDisposition {
    let refusals = members
        .iter()
        .filter_map(|projection| match projection.disposition {
            RegisterProjectionDisposition::Refused { reason } => Some(reason),
            RegisterProjectionDisposition::Bound { .. } => None,
        })
        .collect::<BTreeSet<_>>();
    if let Some(reason) = refusals.iter().next().copied() {
        return RegisterProjectionComponentDisposition::Refused {
            reason: if refusals.len() == 1 {
                reason
            } else {
                RegisterProjectionRefusal::AmbiguousContainingCarrier
            },
        };
    }

    let carriers = members
        .iter()
        .filter_map(|projection| match projection.disposition {
            RegisterProjectionDisposition::Bound { carrier, .. } => Some(carrier),
            RegisterProjectionDisposition::Refused { .. } => None,
        })
        .collect::<BTreeSet<_>>();
    let Some(carrier) = carriers.iter().next().copied() else {
        return RegisterProjectionComponentDisposition::Refused {
            reason: RegisterProjectionRefusal::NoContainingCarrier,
        };
    };
    if carriers.len() != 1 {
        return RegisterProjectionComponentDisposition::Refused {
            reason: RegisterProjectionRefusal::AmbiguousContainingCarrier,
        };
    }

    let carrier_end = carrier
        .checked_end()
        .expect("validated carrier storage has an end");
    let mut little_possible = true;
    let mut big_possible = true;
    for projection in members {
        let RegisterProjectionDisposition::Bound { slice, .. } = projection.disposition else {
            unreachable!("validated component cannot mix bound and refused projections")
        };
        let written_end = projection
            .written
            .checked_end()
            .expect("validated written storage has an end");
        let little_offset = projection
            .written
            .offset
            .checked_sub(carrier.offset)
            .and_then(|offset| offset.checked_mul(8));
        let big_offset = carrier_end
            .checked_sub(written_end)
            .and_then(|offset| offset.checked_mul(8));
        little_possible &= little_offset == Some(slice.lsb_bit_offset);
        big_possible &= big_offset == Some(slice.lsb_bit_offset);
    }
    let inferred_byte_order = match (little_possible, big_possible) {
        (true, false) => Some(RegisterByteOrder::Little),
        (false, true) => Some(RegisterByteOrder::Big),
        (true, true) | (false, false) => None,
    };
    let byte_order = match source_byte_order {
        Err(reason) => {
            return RegisterProjectionComponentDisposition::Refused { reason };
        }
        Ok(Some(RegisterByteOrder::Little)) if !little_possible => {
            return RegisterProjectionComponentDisposition::Refused {
                reason: RegisterProjectionRefusal::ConflictingDeclarations,
            };
        }
        Ok(Some(RegisterByteOrder::Big)) if !big_possible => {
            return RegisterProjectionComponentDisposition::Refused {
                reason: RegisterProjectionRefusal::ConflictingDeclarations,
            };
        }
        Ok(Some(byte_order)) => Some(byte_order),
        Ok(None) => inferred_byte_order,
    };
    RegisterProjectionComponentDisposition::Bound {
        carrier,
        byte_order,
    }
}

/// Instruction pattern and its semantic definition.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstructionDef {
    /// Instruction mnemonic
    pub mnemonic: String,
    /// P-code operations for this instruction pattern
    pub ops: Vec<R2ILOp>,
}

/// Complete architecture specification.
///
/// This is the top-level structure serialized to `.r2il` files.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArchSpec {
    /// Architecture name (e.g., "x86", "x86-64", "ARM")
    pub name: String,

    /// Processor variant (e.g., "default", "thumb")
    pub variant: String,

    /// Endianness for instruction encoding/fetch semantics.
    pub instruction_endianness: Endianness,

    /// Endianness for memory load/store semantics.
    pub memory_endianness: Endianness,

    /// Address size in bytes (4 for 32-bit, 8 for 64-bit)
    pub addr_size: u32,

    /// Alignment requirement
    pub alignment: u32,

    /// Address spaces
    pub spaces: Vec<AddressSpace>,

    /// Register definitions
    pub registers: Vec<RegisterDef>,

    /// Name-free register carrier geometry, sorted by `written` storage.
    ///
    /// An empty table means the architecture source did not provide this
    /// contract. A non-empty table covers every unique declared register
    /// storage exactly once.
    pub register_projections: Vec<RegisterProjection>,

    /// Registers this architecture's calling convention returns a value in, in
    /// preference order.
    ///
    /// A consumer asking which register holds a returned value has three
    /// sources: the recovered function interface, the recovered convention, and
    /// failing both, the architecture itself. Without this last one there is no
    /// answer at all for a binary whose ABI was never recovered, and the only
    /// remaining option is a hand-written list of register spellings that knows
    /// the architectures somebody thought of.
    #[serde(default)]
    pub return_registers: Vec<RegisterDef>,

    /// The names of the language's user-defined p-code operations, indexed by
    /// the identifier a `CallOther` carries.
    ///
    /// A `CallOther` states only that index, and the index is assigned by the
    /// compiled specification and moves with it, so nothing can say which
    /// operation an instruction invoked without this list. An empty table means
    /// the architecture source did not provide one, and every `CallOther` then
    /// stays unidentified rather than being guessed at.
    #[serde(default)]
    pub user_ops: Vec<String>,
}

impl ArchSpec {
    /// Create a new architecture specification.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            variant: "default".into(),
            instruction_endianness: Endianness::Little,
            memory_endianness: Endianness::Little,
            addr_size: 8,
            alignment: 1,
            spaces: Vec::new(),
            registers: Vec::new(),
            register_projections: Vec::new(),
            return_registers: Vec::new(),
            user_ops: Vec::new(),
        }
    }

    /// State which registers this architecture returns a value in.
    pub fn with_return_registers(
        mut self,
        registers: impl IntoIterator<Item = RegisterDef>,
    ) -> Self {
        self.return_registers = registers.into_iter().collect();
        self
    }

    /// Set instruction endianness.
    pub fn set_instruction_endianness(&mut self, endianness: Endianness) {
        self.instruction_endianness = endianness;
    }

    /// Set memory endianness.
    pub fn set_memory_endianness(&mut self, endianness: Endianness) {
        self.memory_endianness = endianness;
    }

    /// Add a register definition.
    pub fn add_register(&mut self, reg: RegisterDef) {
        self.registers.push(reg);
    }

    /// Add an address space.
    pub fn add_space(&mut self, space: AddressSpace) {
        self.spaces.push(space);
    }

    /// Look up a register by name.
    pub fn get_register(&self, name: &str) -> Option<&RegisterDef> {
        self.registers.iter().find(|r| r.name == name)
    }

    /// Look up source-owned register geometry in `O(log n)` time.
    ///
    /// Returns `None` when geometry is unavailable or the storage was not
    /// declared. Validation guarantees that a non-empty table is sorted and
    /// complete.
    pub fn register_projection(&self, written: RegisterStorage) -> Option<&RegisterProjection> {
        let index = self
            .register_projections
            .binary_search_by_key(&written, |projection| projection.written)
            .ok()?;
        self.register_projections.get(index)
    }
}

fn encode_current<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    Ok(postcard::to_stdvec(value)?)
}

fn decode_current<T: for<'de> Deserialize<'de>>(bytes: &[u8]) -> Result<T> {
    let (value, remainder) = postcard::take_from_bytes(bytes)?;
    if !remainder.is_empty() {
        return Err(SerializeError::TrailingBytes(remainder.len()));
    }
    Ok(value)
}

/// Save an architecture specification to a file.
pub fn save(arch: &ArchSpec, path: &Path) -> Result<()> {
    std::fs::write(path, to_bytes(arch)?)?;
    Ok(())
}

/// Load an architecture specification from a file.
pub fn load(path: &Path) -> Result<ArchSpec> {
    from_bytes(&std::fs::read(path)?)
}

/// Save to bytes (for testing or embedding).
pub fn to_bytes(arch: &ArchSpec) -> Result<Vec<u8>> {
    crate::validate_archspec(arch)?;
    let arch_bytes = encode_current(arch)?;
    let payload_len =
        u64::try_from(arch_bytes.len()).map_err(|_| SerializeError::PayloadTooLarge(u64::MAX))?;
    let capacity = MAGIC
        .len()
        .checked_add(size_of::<u64>())
        .and_then(|header| header.checked_add(arch_bytes.len()))
        .ok_or(SerializeError::PayloadTooLarge(payload_len))?;
    let mut bytes = Vec::with_capacity(capacity);
    bytes.extend_from_slice(MAGIC);
    bytes.extend_from_slice(&payload_len.to_le_bytes());
    bytes.extend_from_slice(&arch_bytes);

    Ok(bytes)
}

/// Load from bytes (for testing or embedded resources).
pub fn from_bytes(bytes: &[u8]) -> Result<ArchSpec> {
    let header_len = MAGIC.len() + size_of::<u64>();
    if bytes.len() < MAGIC.len() {
        return Err(SerializeError::Truncated);
    }
    if &bytes[..MAGIC.len()] != MAGIC {
        return Err(SerializeError::InvalidMagic);
    }
    if bytes.len() < header_len {
        return Err(SerializeError::Truncated);
    }
    let payload_len_u64 = u64::from_le_bytes(
        bytes[MAGIC.len()..header_len]
            .try_into()
            .expect("checked fixed payload length"),
    );
    let payload_len = usize::try_from(payload_len_u64)
        .map_err(|_| SerializeError::PayloadTooLarge(payload_len_u64))?;
    let expected_len = header_len
        .checked_add(payload_len)
        .ok_or(SerializeError::PayloadTooLarge(payload_len_u64))?;
    if bytes.len() < expected_len {
        return Err(SerializeError::Truncated);
    }
    if bytes.len() > expected_len {
        return Err(SerializeError::TrailingBytes(bytes.len() - expected_len));
    }
    decode_archspec_bytes(&bytes[header_len..expected_len])
}

fn decode_archspec_bytes(bytes: &[u8]) -> Result<ArchSpec> {
    let arch: ArchSpec = decode_current(bytes)?;
    crate::validate_archspec(&arch)?;
    Ok(arch)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn valid_arch(name: &str) -> ArchSpec {
        let mut arch = ArchSpec::new(name);
        arch.add_space(AddressSpace::ram(8));
        arch.add_space(AddressSpace::register());
        arch
    }

    fn frame_payload(payload: &[u8]) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(MAGIC.len() + size_of::<u64>() + payload.len());
        bytes.extend_from_slice(MAGIC);
        bytes.extend_from_slice(
            &u64::try_from(payload.len())
                .expect("test payload length fits u64")
                .to_le_bytes(),
        );
        bytes.extend_from_slice(payload);
        bytes
    }

    #[test]
    fn test_roundtrip() {
        let mut arch = ArchSpec::new("test-arch");
        arch.set_memory_endianness(Endianness::Little);
        arch.set_instruction_endianness(Endianness::Little);
        arch.addr_size = 8;

        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::sub("EAX", 0, 4, "RAX"));
        let rax = RegisterStorage { offset: 0, size: 8 };
        let eax = RegisterStorage { offset: 0, size: 4 };
        arch.register_projections = vec![
            RegisterProjection {
                written: eax,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: rax,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 32,
                    },
                },
            },
            RegisterProjection {
                written: rax,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: rax,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 64,
                    },
                },
            },
        ];

        arch.add_space(AddressSpace::ram(8));
        arch.add_space(AddressSpace::register());

        // Serialize and deserialize
        let bytes = to_bytes(&arch).unwrap();
        let loaded = from_bytes(&bytes).unwrap();

        assert_eq!(loaded.name, "test-arch");
        assert_eq!(loaded.instruction_endianness, Endianness::Little);
        assert_eq!(loaded.memory_endianness, Endianness::Little);
        assert_eq!(loaded.addr_size, 8);
        assert_eq!(loaded.registers.len(), 2);
        assert_eq!(loaded.register_projections, arch.register_projections);
        assert_eq!(
            loaded.register_projection(eax),
            Some(&arch.register_projections[0])
        );
        assert_eq!(
            loaded.register_projection(rax),
            Some(&arch.register_projections[1])
        );
        assert_eq!(
            loaded.register_projection(RegisterStorage { offset: 8, size: 8 }),
            None
        );
        assert_eq!(loaded.spaces.len(), 2);
        assert_eq!(&bytes[..MAGIC.len()], MAGIC);
    }

    #[test]
    fn test_invalid_magic() {
        let bytes = b"NOTR2IL!";
        let result = from_bytes(bytes);
        assert!(matches!(result, Err(SerializeError::InvalidMagic)));
    }

    #[test]
    fn previous_format_discriminator_is_rejected() {
        let mut bytes = to_bytes(&valid_arch("previous-format")).expect("serialize fixture");
        bytes[..MAGIC.len()].copy_from_slice(b"R2PSTC06");
        assert!(matches!(
            from_bytes(&bytes),
            Err(SerializeError::InvalidMagic)
        ));
    }

    #[test]
    fn current_roundtrip_preserves_typed_geometry_refusals() {
        let mut arch = valid_arch("projection-refusal");
        let first = RegisterStorage { offset: 0, size: 4 };
        let second = RegisterStorage { offset: 2, size: 4 };
        arch.add_register(RegisterDef::new("first", first.offset, first.size));
        arch.add_register(RegisterDef::new("second", second.offset, second.size));
        arch.register_projections = vec![
            RegisterProjection {
                written: first,
                disposition: RegisterProjectionDisposition::Refused {
                    reason: RegisterProjectionRefusal::PartialOverlap,
                },
            },
            RegisterProjection {
                written: second,
                disposition: RegisterProjectionDisposition::Refused {
                    reason: RegisterProjectionRefusal::PartialOverlap,
                },
            },
        ];

        let loaded = from_bytes(&to_bytes(&arch).expect("serialize")).expect("deserialize");
        assert_eq!(loaded.register_projections, arch.register_projections);
    }

    #[test]
    fn canonical_projection_query_certifies_unnamed_little_endian_lanes() {
        let q0 = RegisterStorage {
            offset: 0x5000,
            size: 16,
        };
        let s0 = RegisterStorage {
            offset: 0x5000,
            size: 4,
        };
        let q4 = RegisterStorage {
            offset: 0x5040,
            size: 16,
        };
        let b4 = RegisterStorage {
            offset: 0x5040,
            size: 1,
        };
        let mut arch = valid_arch("aarch64-vector-lanes");
        for (name, storage) in [("q0", q0), ("s0", s0), ("q4", q4), ("b4", b4)] {
            arch.add_register(RegisterDef::new(name, storage.offset, storage.size));
        }
        arch.register_projections = vec![
            RegisterProjection {
                written: s0,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: q0,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 32,
                    },
                },
            },
            RegisterProjection {
                written: q0,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: q0,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 128,
                    },
                },
            },
            RegisterProjection {
                written: b4,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: q4,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 8,
                    },
                },
            },
            RegisterProjection {
                written: q4,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: q4,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 128,
                    },
                },
            },
        ];

        let query = RegisterProjectionQuery::from_arch(&arch)
            .expect("valid source geometry")
            .expect("available source geometry");
        let word_lane = RegisterStorage {
            offset: 0x5004,
            size: 4,
        };
        assert_eq!(
            query.project(word_lane),
            RegisterProjection {
                written: word_lane,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: q0,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 32,
                        size_bits: 32,
                    },
                },
            }
        );
        let byte_lane = RegisterStorage {
            offset: 0x5041,
            size: 1,
        };
        assert_eq!(
            query.project(byte_lane),
            RegisterProjection {
                written: byte_lane,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: q4,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 8,
                        size_bits: 8,
                    },
                },
            }
        );
    }

    #[test]
    fn canonical_projection_query_refuses_unproved_subranges() {
        let carrier = RegisterStorage { offset: 0, size: 8 };
        let mut missing_orientation = valid_arch("missing-register-byte-order");
        missing_orientation.add_register(RegisterDef::new("carrier", 0, 8));
        missing_orientation.register_projections = vec![RegisterProjection {
            written: carrier,
            disposition: RegisterProjectionDisposition::Bound {
                carrier,
                slice: RegisterBitSlice {
                    lsb_bit_offset: 0,
                    size_bits: 64,
                },
            },
        }];
        let query = RegisterProjectionQuery::from_arch(&missing_orientation)
            .expect("valid geometry")
            .expect("available geometry");
        assert_eq!(
            query.project(RegisterStorage { offset: 1, size: 1 }),
            RegisterProjection {
                written: RegisterStorage { offset: 1, size: 1 },
                disposition: RegisterProjectionDisposition::Refused {
                    reason: RegisterProjectionRefusal::MissingRegisterEndianness,
                },
            }
        );

        let mut source_certified = missing_orientation.clone();
        source_certified.name = "source-certified-register-byte-order".to_string();
        source_certified
            .spaces
            .iter_mut()
            .find(|space| space.id == crate::SpaceId::Register)
            .expect("register space")
            .endianness = Some(Endianness::Little);
        let query = RegisterProjectionQuery::from_arch(&source_certified)
            .expect("valid source-certified geometry")
            .expect("available source-certified geometry");
        assert_eq!(
            query.project(RegisterStorage { offset: 1, size: 1 }),
            RegisterProjection {
                written: RegisterStorage { offset: 1, size: 1 },
                disposition: RegisterProjectionDisposition::Bound {
                    carrier,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 8,
                        size_bits: 8,
                    },
                },
            }
        );

        let mut contradictory = source_certified;
        contradictory.name = "contradictory-register-byte-order".to_string();
        contradictory
            .spaces
            .iter_mut()
            .find(|space| space.id == crate::SpaceId::Register)
            .expect("register space")
            .endianness = Some(Endianness::Big);
        contradictory.register_projections.push(RegisterProjection {
            written: RegisterStorage { offset: 0, size: 4 },
            disposition: RegisterProjectionDisposition::Bound {
                carrier,
                slice: RegisterBitSlice {
                    lsb_bit_offset: 0,
                    size_bits: 32,
                },
            },
        });
        contradictory.add_register(RegisterDef::new("low", 0, 4));
        contradictory
            .register_projections
            .sort_by_key(|projection| projection.written);
        let query = RegisterProjectionQuery::from_arch(&contradictory)
            .expect("internally valid but source-contradictory geometry")
            .expect("available source-contradictory geometry");
        assert_eq!(
            query
                .project(RegisterStorage { offset: 1, size: 1 })
                .disposition,
            RegisterProjectionDisposition::Refused {
                reason: RegisterProjectionRefusal::ConflictingDeclarations,
            }
        );
        assert_eq!(
            query
                .project(RegisterStorage {
                    offset: u64::MAX,
                    size: 2,
                })
                .disposition,
            RegisterProjectionDisposition::Refused {
                reason: RegisterProjectionRefusal::InvalidStorageRange,
            }
        );
        assert_eq!(
            query
                .project(RegisterStorage {
                    offset: 0x100,
                    size: 1,
                })
                .disposition,
            RegisterProjectionDisposition::Refused {
                reason: RegisterProjectionRefusal::NoContainingCarrier,
            }
        );

        let first = RegisterStorage { offset: 0, size: 8 };
        let second = RegisterStorage { offset: 4, size: 8 };
        let mut partial = valid_arch("partial-overlap");
        partial.add_register(RegisterDef::new("first", 0, 8));
        partial.add_register(RegisterDef::new("second", 4, 8));
        partial.register_projections = [first, second]
            .into_iter()
            .map(|written| RegisterProjection {
                written,
                disposition: RegisterProjectionDisposition::Refused {
                    reason: RegisterProjectionRefusal::PartialOverlap,
                },
            })
            .collect();
        let query = RegisterProjectionQuery::from_arch(&partial)
            .expect("typed partial-overlap geometry")
            .expect("available refused geometry");
        assert_eq!(
            query
                .project(RegisterStorage { offset: 5, size: 1 })
                .disposition,
            RegisterProjectionDisposition::Refused {
                reason: RegisterProjectionRefusal::PartialOverlap,
            }
        );
    }

    #[test]
    fn every_truncated_discriminator_prefix_is_rejected_consistently() {
        let encoded = to_bytes(&valid_arch("truncation")).expect("serialize fixture");
        let path =
            std::env::temp_dir().join(format!("r2il-truncation-{}.r2il", std::process::id()));
        for length in 0..encoded.len() {
            assert!(
                matches!(
                    from_bytes(&encoded[..length]),
                    Err(SerializeError::Truncated)
                ),
                "prefix length {length} must be truncated"
            );
            std::fs::write(&path, &encoded[..length]).expect("write truncated fixture");
            assert!(
                matches!(load(&path), Err(SerializeError::Truncated)),
                "file prefix length {length} must be truncated"
            );
        }
        std::fs::remove_file(path).expect("remove truncated fixture");
    }

    #[test]
    fn archspec_defaults_use_little_endianness_current() {
        let arch = ArchSpec::new("default");
        assert_eq!(arch.instruction_endianness, Endianness::Little);
        assert_eq!(arch.memory_endianness, Endianness::Little);
    }

    #[test]
    fn current_roundtrip_preserves_instruction_and_memory_endianness() {
        let mut arch = valid_arch("mixed-scope");
        arch.set_instruction_endianness(Endianness::Big);
        arch.set_memory_endianness(Endianness::Little);

        let bytes = to_bytes(&arch).expect("serialize");
        let loaded = from_bytes(&bytes).expect("deserialize");
        assert_eq!(loaded.instruction_endianness, Endianness::Big);
        assert_eq!(loaded.memory_endianness, Endianness::Little);
        assert_eq!(&bytes[..MAGIC.len()], MAGIC);
    }

    #[test]
    fn current_roundtrip_preserves_topology_fields() {
        let mut arch = ArchSpec::new("topology-current");
        let mut ram = AddressSpace::ram(8);
        ram.memory_class = Some(crate::MemoryClass::Mmio);
        ram.permissions = Some(crate::MemoryPermissions {
            read: true,
            write: true,
            execute: false,
            volatile: false,
            cacheable: true,
        });
        ram.valid_ranges.push(crate::MemoryRange {
            start: 0x1000,
            end: 0x2000,
        });
        ram.bank_id = Some("bank0".to_string());
        ram.segment_id = Some("seg0".to_string());
        arch.add_space(ram.clone());

        let bytes = to_bytes(&arch).expect("serialize");
        let loaded = from_bytes(&bytes).expect("deserialize");
        assert_eq!(&bytes[..MAGIC.len()], MAGIC);
        assert_eq!(loaded.spaces.len(), 1);
        assert_eq!(loaded.spaces[0].memory_class, ram.memory_class);
        assert_eq!(loaded.spaces[0].permissions, ram.permissions);
        assert_eq!(loaded.spaces[0].valid_ranges, ram.valid_ranges);
        assert_eq!(loaded.spaces[0].bank_id, ram.bank_id);
        assert_eq!(loaded.spaces[0].segment_id, ram.segment_id);
    }

    #[test]
    fn save_writes_only_the_current_format_discriminator() {
        let arch = valid_arch("current-format");
        let bytes = to_bytes(&arch).expect("serialize");
        assert_eq!(&bytes[..MAGIC.len()], MAGIC);
    }

    #[test]
    fn old_v4_header_length_collision_cannot_enter_current_decoder() {
        let mut old = Vec::from(b"R2IL".as_slice());
        old.extend_from_slice(&5_u32.to_le_bytes());
        old.extend_from_slice(&[4, 3, b'x', b'8', b'6']);
        old.extend_from_slice(&encode_current(&valid_arch("x86")).expect("legacy-shaped payload"));
        assert!(matches!(
            from_bytes(&old),
            Err(SerializeError::InvalidMagic)
        ));

        let mut adversarial = Vec::from(b"R2IL".as_slice());
        adversarial.extend_from_slice(&u32::from_le_bytes(*b"PST5").to_le_bytes());
        assert!(matches!(
            from_bytes(&adversarial),
            Err(SerializeError::InvalidMagic)
        ));
    }

    #[test]
    fn trailing_payload_bytes_are_rejected() {
        let arch = valid_arch("trailing");
        let mut bytes = to_bytes(&arch).expect("serialize");
        bytes.push(0);
        assert!(matches!(
            from_bytes(&bytes),
            Err(SerializeError::TrailingBytes(1))
        ));
    }

    #[test]
    fn exact_length_malformed_postcard_payload_is_rejected() {
        let bytes = frame_payload(&[0xff]);
        assert!(matches!(
            from_bytes(&bytes),
            Err(SerializeError::Postcard(_))
        ));
    }

    #[test]
    fn current_frame_cannot_bypass_architecture_validation() {
        let invalid = ArchSpec::new("missing-spaces");
        assert!(matches!(
            to_bytes(&invalid),
            Err(SerializeError::Validation(_))
        ));

        let payload = encode_current(&invalid).expect("encode deliberately invalid payload");
        assert!(matches!(
            from_bytes(&frame_payload(&payload)),
            Err(SerializeError::Validation(_))
        ));
    }
}
