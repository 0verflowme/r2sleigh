//! Memory semantics and topology model for r2il.
//!
//! This module defines ordering, permissions, ranges, and atomic-kind hints.

use serde::{Deserialize, Serialize};

/// Memory ordering semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum MemoryOrdering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
    #[default]
    Unknown,
}

/// Memory access permissions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(default)]
pub struct MemoryPermissions {
    /// Read capability.
    pub read: bool,
    /// Write capability.
    pub write: bool,
    /// Execute capability.
    pub execute: bool,
    /// Access is volatile (side effects / no elision).
    pub volatile: bool,
    /// Access is cacheable.
    pub cacheable: bool,
}

/// Valid memory range expressed as a half-open interval `[start, end)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryRange {
    pub start: u64,
    pub end: u64,
}

impl MemoryRange {
    /// Returns true when the given access interval is fully contained.
    pub fn contains_interval(&self, start: u64, size: u32) -> bool {
        let Some(end) = start.checked_add(size as u64) else {
            return false;
        };
        start >= self.start && end <= self.end
    }
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    #[kani::proof]
    fn contains_interval_matches_half_open_math() {
        let range = MemoryRange {
            start: kani::any(),
            end: kani::any(),
        };
        let start: u64 = kani::any();
        let size: u32 = kani::any();

        let got = range.contains_interval(start, size);
        let expected = start
            .checked_add(size as u64)
            .is_some_and(|end| start >= range.start && end <= range.end);

        assert_eq!(got, expected);

        if got {
            let end = start.checked_add(size as u64).unwrap();
            assert!(range.start <= start);
            assert!(start <= end);
            assert!(end <= range.end);
        }
    }
}

/// Atomic operation kind hint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum AtomicKind {
    LoadLinked,
    StoreConditional,
    CompareExchange,
    ReadModifyWrite,
    Fence,
    #[default]
    Unknown,
}

#[cfg(test)]
mod tests {
    use super::{AtomicKind, MemoryOrdering, MemoryPermissions, MemoryRange};

    #[test]
    fn memory_ordering_serde_roundtrip() {
        let json = serde_json::to_string(&MemoryOrdering::AcqRel).expect("serialize");
        let decoded: MemoryOrdering = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(decoded, MemoryOrdering::AcqRel);
    }

    #[test]
    fn atomic_kind_serde_roundtrip() {
        let json = serde_json::to_string(&AtomicKind::ReadModifyWrite).expect("serialize");
        let decoded: AtomicKind = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(decoded, AtomicKind::ReadModifyWrite);
    }

    #[test]
    fn memory_permissions_serde_roundtrip() {
        let perms = MemoryPermissions {
            read: true,
            write: false,
            execute: true,
            volatile: true,
            cacheable: false,
        };
        let json = serde_json::to_string(&perms).expect("serialize");
        let decoded: MemoryPermissions = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(decoded, perms);
    }

    #[test]
    fn memory_permissions_serde_defaults_new_fields() {
        let json = r#"{"read":true,"write":false,"execute":false}"#;
        let decoded: MemoryPermissions = serde_json::from_str(json).expect("deserialize");
        assert!(decoded.read);
        assert!(!decoded.write);
        assert!(!decoded.execute);
        assert!(!decoded.volatile);
        assert!(!decoded.cacheable);
    }

    #[test]
    fn memory_range_contains_interval() {
        let range = MemoryRange {
            start: 0x1000,
            end: 0x1100,
        };
        assert!(range.contains_interval(0x1000, 4));
        assert!(range.contains_interval(0x10fc, 4));
        assert!(!range.contains_interval(0x10fd, 4));
        assert!(!range.contains_interval(0x0ff0, 4));
    }
}
