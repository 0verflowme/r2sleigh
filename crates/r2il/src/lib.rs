//! r2il - Intermediate Language for r2sleigh
//!
//! This crate provides the core types for the r2il intermediate language,
//! which represents processor instruction semantics in a strongly-typed format.
//!
//! # Architecture
//!
//! r2il is based on Ghidra's P-code, with the following components:
//!
//! - [`Varnode`]: A sized piece of data at a specific location (register, memory, constant, or temporary)
//! - [`SpaceId`]: Identifies the address space (RAM, register, unique, const)
//! - [`R2ILOp`]: A single semantic operation (copy, add, load, store, branch, etc.)
//! - [`R2ILBlock`]: A sequence of operations for a single instruction
//! - [`ArchSpec`]: Full architecture specification with registers and instruction semantics
//!
//! # Example
//!
//! ```rust
//! use r2il::{Varnode, R2ILOp, R2ILBlock};
//!
//! // Represent: MOV EAX, 42
//! let eax = Varnode::register(0, 4);  // EAX at offset 0, size 4
//! let imm = Varnode::constant(42, 4); // Immediate value 42, size 4
//!
//! let mut block = R2ILBlock::new(0x1000, 5);
//! block.push(R2ILOp::Copy { dst: eax, src: imm });
//! ```

pub mod endianness;
pub mod memory;
pub mod metadata;
pub mod opcode;
pub mod regname;
pub mod serialize;
pub mod space;
pub mod validate;
pub mod varnode;

// Re-export main types at crate root
pub use endianness::Endianness;
pub use memory::{AtomicKind, MemoryOrdering, MemoryPermissions, MemoryRange};
pub use metadata::{
    FloatEncodingHint, MemoryClass, OpMetadata, PointerHint, ScalarKind, StorageClass,
    VarnodeMetadata,
};
pub use opcode::{R2ILBlock, R2ILOp, SwitchCase, SwitchInfo};
pub use regname::select_register_name;
pub use serialize::{ArchSpec, RegisterDef};
pub use space::{AddressSpace, SpaceId};
pub use validate::{
    ValidationError, ValidationIssue, effective_arch_address_size, validate_archspec,
    validate_block, validate_block_full, validate_block_semantic, validate_op,
    validate_op_semantic,
};
pub use varnode::Varnode;

/// Exact discriminator for the sole supported postcard representation.
pub const MAGIC: &[u8; 8] = b"R2PSTC05";
