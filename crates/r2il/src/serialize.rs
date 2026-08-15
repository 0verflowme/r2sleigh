//! Serialization support for r2il types.
//!
//! This module provides binary serialization using postcard for efficient
//! storage and loading of architecture specifications.

use serde::{Deserialize, Serialize};
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

    #[error("Invalid format discriminator: expected R2PSTC06")]
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
        }
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
        bytes[..MAGIC.len()].copy_from_slice(b"R2PSTC05");
        assert!(matches!(
            from_bytes(&bytes),
            Err(SerializeError::InvalidMagic)
        ));
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
