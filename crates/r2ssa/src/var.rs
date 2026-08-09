//! SSA variable representation.

use serde::{Deserialize, Serialize};

/// Name-independent storage identity retained from the lifted varnode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum CanonicalStorageSpace {
    Ram,
    Register,
    Unique,
    Constant,
    Custom(u32),
    /// Programmatically synthesized SSA with no lifted storage provenance.
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CanonicalStorageId {
    pub space: CanonicalStorageSpace,
    pub offset: u64,
    pub size: u32,
}

impl CanonicalStorageId {
    pub const fn from_varnode(varnode: &r2il::Varnode) -> Self {
        let space = match varnode.space {
            r2il::SpaceId::Ram => CanonicalStorageSpace::Ram,
            r2il::SpaceId::Register => CanonicalStorageSpace::Register,
            r2il::SpaceId::Unique => CanonicalStorageSpace::Unique,
            r2il::SpaceId::Const => CanonicalStorageSpace::Constant,
            r2il::SpaceId::Custom(id) => CanonicalStorageSpace::Custom(id),
        };
        Self {
            space,
            offset: varnode.offset,
            size: varnode.size,
        }
    }

    pub const fn unknown(ordinal: u64, size: u32) -> Self {
        Self {
            space: CanonicalStorageSpace::Unknown,
            offset: ordinal,
            size,
        }
    }

    pub const fn is_unknown(self) -> bool {
        matches!(self.space, CanonicalStorageSpace::Unknown)
    }
}

/// Canonical classification for SSA variable names.
///
/// Raw SSA names still carry prefixes because they originate at the IL/lift
/// seam. Consumers should ask this type for the meaning of those names instead
/// of re-parsing prefix strings in downstream crates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SSAVarNameKind {
    RegisterAlias,
    Temporary,
    Constant,
    Memory,
    AddressSpace,
    Symbol,
    Object,
    Data,
    Got,
    Ordinary,
}

impl SSAVarNameKind {
    pub fn classify(name: &str) -> Self {
        if name.strip_prefix("reg:").is_some() {
            Self::RegisterAlias
        } else if name.strip_prefix("tmp:").is_some() || name.strip_prefix("unique:").is_some() {
            Self::Temporary
        } else if name.strip_prefix("const:").is_some() {
            Self::Constant
        } else if name.strip_prefix("ram:").is_some() {
            Self::Memory
        } else if name.strip_prefix("space").is_some() {
            Self::AddressSpace
        } else if name.strip_prefix("sym.").is_some() {
            Self::Symbol
        } else if name.strip_prefix("obj.").is_some() {
            Self::Object
        } else if name.strip_prefix("data.").is_some() {
            Self::Data
        } else if name.strip_prefix("got.").is_some() {
            Self::Got
        } else {
            Self::Ordinary
        }
    }

    pub fn is_prefixed_display_name(self) -> bool {
        matches!(
            self,
            Self::RegisterAlias
                | Self::Temporary
                | Self::Constant
                | Self::Memory
                | Self::AddressSpace
        )
    }

    pub fn is_constant(self) -> bool {
        matches!(self, Self::Constant)
    }

    pub fn is_temporary(self) -> bool {
        matches!(self, Self::Temporary)
    }

    pub fn is_memory(self) -> bool {
        matches!(self, Self::Memory)
    }

    pub fn is_address_space(self) -> bool {
        matches!(self, Self::AddressSpace)
    }

    pub fn is_global_symbol(self) -> bool {
        matches!(self, Self::Symbol | Self::Object | Self::Data | Self::Got)
    }

    pub fn strip_constant_prefix(name: &str) -> Option<&str> {
        name.strip_prefix("const:")
    }

    pub fn strip_temporary_prefix(name: &str) -> Option<&str> {
        name.strip_prefix("tmp:")
            .or_else(|| name.strip_prefix("unique:"))
    }
}

/// An SSA variable: a named location with a version number.
///
/// In SSA form, each assignment creates a new version of the variable.
/// For example, if `RAX` is written twice, we get `RAX_0` and `RAX_1`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SSAVar {
    /// The base name of the variable (e.g., "RAX", "tmp:0x1000", "const:0x42").
    pub name: String,
    /// The version number (0 for initial/input, incremented on each write).
    pub version: u32,
    /// Size in bytes.
    pub size: u32,
    /// Exact source bitvector for constants.
    ///
    /// This is semantic data. The `name` field is presentation-only and must
    /// not be parsed by proof-bearing consumers to recover a constant value.
    #[serde(default)]
    constant_bits: Option<u64>,
}

impl SSAVar {
    /// Create a new SSA variable.
    pub fn new(name: impl Into<String>, version: u32, size: u32) -> Self {
        Self {
            name: name.into(),
            version,
            size,
            constant_bits: None,
        }
    }

    /// Create the initial (version 0) variable.
    pub fn initial(name: impl Into<String>, size: u32) -> Self {
        Self::new(name, 0, size)
    }

    /// Create a constant SSA variable.
    pub fn constant(value: u64, size: u32) -> Self {
        Self {
            name: format!("const:{:x}", value),
            version: 0,
            size,
            constant_bits: Some(value),
        }
    }

    /// Create the next version of this variable.
    ///
    /// Returns `None` when the version counter is exhausted instead of
    /// silently wrapping and aliasing a different SSA definition.
    pub fn next_version(&self) -> Option<Self> {
        Some(Self {
            name: self.name.clone(),
            version: self.version.checked_add(1)?,
            size: self.size,
            constant_bits: self.constant_bits,
        })
    }

    /// Return the source bitvector carried by a constant SSA value.
    ///
    /// Unlike legacy helpers that parse `name`, this accessor is safe to use
    /// as semantic evidence.
    pub const fn constant_bits(&self) -> Option<u64> {
        self.constant_bits
    }

    /// Get a display name like "RAX_0" or "RAX_1".
    ///
    /// For named registers (without prefix), outputs "RAX_0".
    /// For unknown registers (with "reg:" prefix), outputs "reg:10_0".
    /// For constants, outputs "const:42_0".
    /// For temporaries, outputs "tmp:1000_0".
    pub fn display_name(&self) -> String {
        // Handle special prefixes (hex fallbacks and other spaces)
        if self.name_kind().is_prefixed_display_name() {
            return format!("{}_{}", self.name, self.version);
        }
        // Named register - uppercase it
        format!("{}_{}", self.name.to_uppercase(), self.version)
    }

    pub fn name_kind(&self) -> SSAVarNameKind {
        SSAVarNameKind::classify(&self.name)
    }

    /// Check if this is a constant SSA value.
    pub fn is_const(&self) -> bool {
        self.name_kind().is_constant()
    }

    /// Check if this is a temporary SSA value.
    pub fn is_temp(&self) -> bool {
        self.name_kind().is_temporary()
    }

    /// Check if this is a memory-backed SSA name (name starts with "ram:").
    pub fn is_memory(&self) -> bool {
        self.name_kind().is_memory()
    }

    /// Check if this is a register (not const or temp).
    pub fn is_register(&self) -> bool {
        !self.is_const() && !self.is_temp()
    }
}

impl std::fmt::Display for SSAVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display_name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ssa_var_creation() {
        let var = SSAVar::new("RAX", 0, 8);
        assert_eq!(var.name, "RAX");
        assert_eq!(var.version, 0);
        assert_eq!(var.size, 8);
        assert_eq!(var.display_name(), "RAX_0");
    }

    #[test]
    fn constants_carry_bits_independently_of_display_names() {
        let constant = SSAVar::constant(0x100000001b3, 8);
        assert_eq!(constant.constant_bits(), Some(0x100000001b3));

        let spoofed_name = SSAVar::new("const:100000001b3", 0, 8);
        assert_eq!(spoofed_name.constant_bits(), None);
    }

    #[test]
    fn test_display_name_preserves_special_prefixes() {
        let cases = [
            ("reg:10", "reg:10_3"),
            ("tmp:0x1000", "tmp:0x1000_3"),
            ("const:0x42", "const:0x42_3"),
            ("ram:0x401000", "ram:0x401000_3"),
            ("space1:0x20", "space1:0x20_3"),
        ];

        for (name, expected) in cases {
            assert_eq!(SSAVar::new(name, 3, 8).display_name(), expected);
        }
    }

    #[test]
    fn test_name_kind_classification() {
        let cases = [
            ("reg:10", SSAVarNameKind::RegisterAlias),
            ("tmp:0x1000", SSAVarNameKind::Temporary),
            ("unique:0x1000", SSAVarNameKind::Temporary),
            ("const:0x42", SSAVarNameKind::Constant),
            ("ram:0x401000", SSAVarNameKind::Memory),
            ("space1:0x20", SSAVarNameKind::AddressSpace),
            ("sym.main", SSAVarNameKind::Symbol),
            ("obj.global", SSAVarNameKind::Object),
            ("data.rel.ro", SSAVarNameKind::Data),
            ("got.printf", SSAVarNameKind::Got),
            ("rax", SSAVarNameKind::Ordinary),
        ];

        for (name, expected) in cases {
            assert_eq!(SSAVarNameKind::classify(name), expected);
            assert_eq!(SSAVar::new(name, 0, 8).name_kind(), expected);
        }
    }

    #[test]
    fn test_name_kind_predicates_and_prefix_stripping() {
        let prefixed_display = [
            SSAVarNameKind::RegisterAlias,
            SSAVarNameKind::Temporary,
            SSAVarNameKind::Constant,
            SSAVarNameKind::Memory,
            SSAVarNameKind::AddressSpace,
        ];
        let non_prefixed_display = [
            SSAVarNameKind::Symbol,
            SSAVarNameKind::Object,
            SSAVarNameKind::Data,
            SSAVarNameKind::Got,
            SSAVarNameKind::Ordinary,
        ];

        for kind in prefixed_display {
            assert!(kind.is_prefixed_display_name());
        }
        for kind in non_prefixed_display {
            assert!(!kind.is_prefixed_display_name());
        }

        for kind in [
            SSAVarNameKind::RegisterAlias,
            SSAVarNameKind::Temporary,
            SSAVarNameKind::Constant,
            SSAVarNameKind::Memory,
            SSAVarNameKind::AddressSpace,
            SSAVarNameKind::Symbol,
            SSAVarNameKind::Object,
            SSAVarNameKind::Data,
            SSAVarNameKind::Got,
            SSAVarNameKind::Ordinary,
        ] {
            assert_eq!(kind.is_constant(), kind == SSAVarNameKind::Constant);
            assert_eq!(kind.is_temporary(), kind == SSAVarNameKind::Temporary);
            assert_eq!(kind.is_memory(), kind == SSAVarNameKind::Memory);
            assert_eq!(
                kind.is_address_space(),
                kind == SSAVarNameKind::AddressSpace
            );
            assert_eq!(
                kind.is_global_symbol(),
                matches!(
                    kind,
                    SSAVarNameKind::Symbol
                        | SSAVarNameKind::Object
                        | SSAVarNameKind::Data
                        | SSAVarNameKind::Got
                )
            );
        }

        assert_eq!(
            SSAVarNameKind::strip_constant_prefix("const:0x42"),
            Some("0x42")
        );
        assert_eq!(SSAVarNameKind::strip_constant_prefix("tmp:0x42"), None);
        assert_eq!(
            SSAVarNameKind::strip_temporary_prefix("tmp:0x1000"),
            Some("0x1000")
        );
        assert_eq!(
            SSAVarNameKind::strip_temporary_prefix("unique:0x1000"),
            Some("0x1000")
        );
        assert_eq!(SSAVarNameKind::strip_temporary_prefix("const:0x1000"), None);
    }

    #[test]
    fn test_next_version() {
        let v0 = SSAVar::initial("RSP", 8);
        let v1 = v0.next_version().expect("version 0 has a successor");
        let v2 = v1.next_version().expect("version 1 has a successor");

        assert_eq!(v0.version, 0);
        assert_eq!(v1.version, 1);
        assert_eq!(v2.version, 2);
        assert_eq!(v0.name, v1.name);
    }

    #[test]
    fn test_next_version_refuses_wraparound() {
        let max = SSAVar::new("RSP", u32::MAX, 8);
        assert_eq!(max.next_version(), None);
    }

    #[test]
    fn test_var_classification() {
        let reg = SSAVar::new("RAX", 0, 8);
        let tmp = SSAVar::new("tmp:0x1000", 0, 4);
        let unique = SSAVar::new("unique:0x1000", 0, 4);
        let cst = SSAVar::new("const:0x42", 0, 4);

        assert!(reg.is_register());
        assert!(!reg.is_temp());
        assert!(!reg.is_const());
        assert!(!reg.is_memory());

        assert!(tmp.is_temp());
        assert!(!tmp.is_const());
        assert!(!tmp.is_register());
        assert!(!tmp.is_memory());

        assert!(unique.is_temp());
        assert!(!unique.is_const());
        assert!(!unique.is_register());
        assert!(!unique.is_memory());

        assert!(cst.is_const());
        assert!(!cst.is_temp());
        assert!(!cst.is_register());
        assert!(!cst.is_memory());

        let mem = SSAVar::new("ram:0x1000", 0, 8);
        assert!(mem.is_memory());
        assert!(!mem.is_const());
        assert!(!mem.is_temp());
    }
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    #[kani::proof]
    fn next_version_is_checked_and_monotonic() {
        let version: u32 = kani::any();
        let size: u32 = kani::any();
        let var = SSAVar::new("rax", version, size);
        let next = var.next_version();

        if version == u32::MAX {
            assert!(next.is_none());
        } else {
            let next = next.expect("non-maximum version has a successor");
            assert_eq!(next.size, var.size);
            assert_eq!(next.version, version + 1);
            assert!(next.version > var.version);
        }
    }
}
