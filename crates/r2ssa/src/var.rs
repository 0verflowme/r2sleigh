//! SSA variable representation.

use serde::{Deserialize, Serialize};

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
}

impl SSAVar {
    /// Create a new SSA variable.
    pub fn new(name: impl Into<String>, version: u32, size: u32) -> Self {
        Self {
            name: name.into(),
            version,
            size,
        }
    }

    /// Create the initial (version 0) variable.
    pub fn initial(name: impl Into<String>, size: u32) -> Self {
        Self::new(name, 0, size)
    }

    /// Create a constant SSA variable.
    pub fn constant(value: u64, size: u32) -> Self {
        Self::new(format!("const:{:x}", value), 0, size)
    }

    /// Create the next version of this variable.
    pub fn next_version(&self) -> Self {
        Self {
            name: self.name.clone(),
            version: self.version + 1,
            size: self.size,
        }
    }

    /// Get a display name like "RAX_0" or "RAX_1".
    ///
    /// For named registers (without prefix), outputs "RAX_0".
    /// For unknown registers (with "reg:" prefix), outputs "reg:10_0".
    /// For constants, outputs "const:42_0".
    /// For temporaries, outputs "tmp:1000_0".
    pub fn display_name(&self) -> String {
        // Handle special prefixes (hex fallbacks and other spaces)
        if self.name.starts_with("reg:")
            || self.name.starts_with("tmp:")
            || self.name.starts_with("const:")
            || self.name.starts_with("ram:")
            || self.name.starts_with("space")
        {
            return format!("{}_{}", self.name, self.version);
        }
        // Named register - uppercase it
        format!("{}_{}", self.name.to_uppercase(), self.version)
    }

    /// Check if this is a constant (name starts with "const:").
    pub fn is_const(&self) -> bool {
        self.name.starts_with("const:")
    }

    /// Check if this is a temporary (name starts with "tmp:").
    pub fn is_temp(&self) -> bool {
        self.name.starts_with("tmp:")
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
    fn test_next_version() {
        let v0 = SSAVar::initial("RSP", 8);
        let v1 = v0.next_version();
        let v2 = v1.next_version();

        assert_eq!(v0.version, 0);
        assert_eq!(v1.version, 1);
        assert_eq!(v2.version, 2);
        assert_eq!(v0.name, v1.name);
    }

    #[test]
    fn test_var_classification() {
        let reg = SSAVar::new("RAX", 0, 8);
        let tmp = SSAVar::new("tmp:0x1000", 0, 4);
        let cst = SSAVar::new("const:0x42", 0, 4);

        assert!(reg.is_register());
        assert!(!reg.is_temp());
        assert!(!reg.is_const());

        assert!(tmp.is_temp());
        assert!(!tmp.is_register());

        assert!(cst.is_const());
        assert!(!cst.is_register());
    }
}
