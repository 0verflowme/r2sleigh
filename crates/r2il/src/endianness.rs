//! Endianness model for r2il.

use serde::{Deserialize, Serialize};

/// Endianness encoding for instruction and memory domains.
///
/// `Mixed` and `Custom` are reserved for forward compatibility in PR5.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum Endianness {
    #[default]
    Little,
    Big,
    Mixed,
    Custom,
}

impl Endianness {
    /// Returns true if this is big-endian.
    pub fn is_big(self) -> bool {
        matches!(self, Self::Big)
    }

    /// Returns true if this is little-endian.
    pub fn is_little(self) -> bool {
        matches!(self, Self::Little)
    }
}

#[cfg(test)]
mod tests {
    use super::Endianness;

    #[test]
    fn endianness_enum_serde_roundtrip() {
        let cases = [
            Endianness::Little,
            Endianness::Big,
            Endianness::Mixed,
            Endianness::Custom,
        ];
        for case in cases {
            let json = serde_json::to_string(&case).expect("serialize");
            let decoded: Endianness = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(decoded, case);
        }
    }
}
