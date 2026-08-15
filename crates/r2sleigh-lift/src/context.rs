//! Architecture context for lifting.
//!
//! This module provides the context needed to translate Sleigh specifications
//! into r2il, including register mappings and address space configuration.

use r2il::{AddressSpace, ArchSpec, Endianness, RegisterDef, SpaceId};
use std::collections::HashMap;

/// Context for translating a specific architecture.
#[derive(Debug)]
pub struct LiftContext {
    /// Architecture specification being built
    pub arch: ArchSpec,

    /// Mapping from Sleigh space names to SpaceId
    space_map: HashMap<String, SpaceId>,

    /// Counter for unique space IDs
    next_custom_space: u32,

    /// Counter for unique temporary offsets
    next_unique_offset: u64,
}

impl LiftContext {
    /// Create a new lift context for an architecture.
    pub fn new(name: impl Into<String>) -> Self {
        let mut ctx = Self {
            arch: ArchSpec::new(name),
            space_map: HashMap::new(),
            next_custom_space: 0,
            next_unique_offset: 0x10000000,
        };

        // Add standard spaces
        ctx.add_standard_spaces();

        ctx
    }

    /// Create a lift context from an existing ArchSpec.
    ///
    /// This is used when we've already parsed a Sleigh spec and have
    /// an ArchSpec ready.
    pub fn from_arch_spec(arch: ArchSpec) -> Self {
        let mut space_map = HashMap::new();

        // Rebuild space map from the arch spec
        for space in &arch.spaces {
            space_map.insert(space.name.clone(), space.id);
        }

        // Also add standard space aliases
        space_map.insert("ram".into(), SpaceId::Ram);
        space_map.insert("register".into(), SpaceId::Register);
        space_map.insert("unique".into(), SpaceId::Unique);
        space_map.insert("const".into(), SpaceId::Const);
        space_map.insert("constant".into(), SpaceId::Const);

        // Find the highest custom space ID
        let next_custom_space = arch
            .spaces
            .iter()
            .filter_map(|s| match s.id {
                SpaceId::Custom(n) => Some(n + 1),
                _ => None,
            })
            .max()
            .unwrap_or(0);

        Self {
            arch,
            space_map,
            next_custom_space,
            next_unique_offset: 0x10000000,
        }
    }

    /// Add the standard address spaces.
    fn add_standard_spaces(&mut self) {
        self.space_map.insert("ram".into(), SpaceId::Ram);
        self.space_map.insert("register".into(), SpaceId::Register);
        self.space_map.insert("unique".into(), SpaceId::Unique);
        self.space_map.insert("const".into(), SpaceId::Const);
        self.space_map.insert("constant".into(), SpaceId::Const);
    }

    /// Set instruction endianness.
    pub fn set_instruction_endianness(&mut self, endianness: Endianness) {
        self.arch.set_instruction_endianness(endianness);
    }

    /// Set memory endianness.
    pub fn set_memory_endianness(&mut self, endianness: Endianness) {
        self.arch.set_memory_endianness(endianness);
    }

    /// Set the address size.
    pub fn set_addr_size(&mut self, size: u32) {
        self.arch.addr_size = size;
    }

    /// Set the alignment.
    pub fn set_alignment(&mut self, align: u32) {
        self.arch.alignment = align;
    }

    /// Add an address space from Sleigh.
    pub fn add_space(&mut self, name: &str, addr_size: u32, is_default: bool) -> SpaceId {
        self.add_space_with_endianness(name, addr_size, is_default, None)
    }

    /// Add an address space with optional endianness override.
    pub fn add_space_with_endianness(
        &mut self,
        name: &str,
        addr_size: u32,
        is_default: bool,
        endianness: Option<Endianness>,
    ) -> SpaceId {
        self.add_space_with_layout(name, addr_size, 1, is_default, endianness)
    }

    /// Add an address space while preserving both the encoded address width
    /// and the number of bytes addressed by one offset unit.
    pub fn add_space_with_layout(
        &mut self,
        name: &str,
        addr_size: u32,
        word_size: u32,
        is_default: bool,
        endianness: Option<Endianness>,
    ) -> SpaceId {
        // Check if it's a standard space
        if let Some(&space_id) = self.space_map.get(name) {
            // Update the existing space definition
            let space = AddressSpace {
                id: space_id,
                name: name.into(),
                addr_size,
                word_size,
                is_default,
                endianness,
                memory_class: None,
                permissions: None,
                valid_ranges: Vec::new(),
                bank_id: None,
                segment_id: None,
            };
            self.arch.add_space(space);
            return space_id;
        }

        // Create a custom space
        let space_id = SpaceId::Custom(self.next_custom_space);
        self.next_custom_space += 1;

        let space = AddressSpace {
            id: space_id,
            name: name.into(),
            addr_size,
            word_size,
            is_default,
            endianness,
            memory_class: None,
            permissions: None,
            valid_ranges: Vec::new(),
            bank_id: None,
            segment_id: None,
        };
        self.arch.add_space(space);
        self.space_map.insert(name.into(), space_id);

        space_id
    }

    /// Look up a space ID by name.
    pub fn get_space(&self, name: &str) -> Option<SpaceId> {
        self.space_map.get(name).copied()
    }

    /// Add a register definition.
    pub fn add_register(&mut self, name: &str, offset: u64, size: u32) {
        let reg = RegisterDef::new(name, offset, size);
        self.arch.add_register(reg);
    }

    /// Add a sub-register definition.
    pub fn add_sub_register(&mut self, name: &str, offset: u64, size: u32, parent: &str) {
        let reg = RegisterDef::sub(name, offset, size, parent);
        self.arch.add_register(reg);
    }

    /// Allocate a unique temporary offset.
    pub fn alloc_unique(&mut self, size: u32) -> u64 {
        let offset = self.next_unique_offset;
        self.next_unique_offset += size as u64;
        offset
    }

    /// Finish building and return the architecture specification.
    pub fn finish(self) -> ArchSpec {
        self.arch
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context_creation() {
        let ctx = LiftContext::new("test");
        assert_eq!(ctx.arch.name, "test");
    }

    #[test]
    fn test_space_mapping() {
        let mut ctx = LiftContext::new("test");

        assert_eq!(ctx.get_space("ram"), Some(SpaceId::Ram));
        assert_eq!(ctx.get_space("register"), Some(SpaceId::Register));
        assert_eq!(ctx.get_space("unique"), Some(SpaceId::Unique));
        assert_eq!(ctx.get_space("const"), Some(SpaceId::Const));

        // Add custom space
        let custom = ctx.add_space("io", 2, false);
        assert!(matches!(custom, SpaceId::Custom(0)));
        assert_eq!(ctx.get_space("io"), Some(SpaceId::Custom(0)));
    }

    #[test]
    fn test_register_addition() {
        let mut ctx = LiftContext::new("test");

        ctx.add_register("RAX", 0, 8);
        ctx.add_sub_register("EAX", 0, 4, "RAX");

        let arch = ctx.finish();
        assert_eq!(arch.registers.len(), 2);
        assert_eq!(arch.get_register("RAX").map(|reg| reg.offset), Some(0));
        assert_eq!(arch.get_register("EAX").map(|reg| reg.offset), Some(0));
    }
}
