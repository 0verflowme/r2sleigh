//! Canonical semantic memory-address evidence.
//!
//! `r2ssa` owns address provenance. This type is the single `r2sym` carrier for
//! exact concrete addresses, exact affine identities, and bounded concrete
//! offset ranges used by backward and VM semantic evidence.

use std::collections::BTreeMap;

use r2ssa::{AffineAddressTerm, RelativeMemoryAddress, ValueId};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(try_from = "SemanticMemoryAddressWire")]
pub struct SemanticMemoryAddress {
    offset_lo: i64,
    offset_hi: i64,
    exact_offset: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    address_terms: Vec<AffineAddressTerm>,
}

#[derive(Debug, Deserialize)]
struct SemanticMemoryAddressWire {
    offset_lo: i64,
    offset_hi: i64,
    exact_offset: bool,
    #[serde(default)]
    address_terms: Vec<AffineAddressTerm>,
}

impl TryFrom<SemanticMemoryAddressWire> for SemanticMemoryAddress {
    type Error = String;

    fn try_from(wire: SemanticMemoryAddressWire) -> Result<Self, Self::Error> {
        Self::new(
            wire.offset_lo,
            wire.offset_hi,
            wire.exact_offset,
            wire.address_terms,
        )
        .ok_or_else(|| "invalid semantic memory address".to_string())
    }
}

impl SemanticMemoryAddress {
    pub fn exact(offset: i64) -> Self {
        Self {
            offset_lo: offset,
            offset_hi: offset,
            exact_offset: true,
            address_terms: Vec::new(),
        }
    }

    pub fn affine(terms: Vec<AffineAddressTerm>, offset: i64) -> Option<Self> {
        Self::new(offset, offset, false, terms).filter(|address| !address.address_terms.is_empty())
    }

    pub fn bounded(offset_lo: i64, offset_hi: i64) -> Option<Self> {
        Self::new(offset_lo, offset_hi, false, Vec::new())
    }

    pub fn from_ssa(address: &RelativeMemoryAddress) -> Option<Self> {
        match address {
            RelativeMemoryAddress::Exact(offset) => Some(Self::exact(*offset)),
            RelativeMemoryAddress::Affine { terms, offset } => Self::affine(terms.clone(), *offset),
            RelativeMemoryAddress::Unknown => None,
        }
    }

    pub const fn offset_lo(&self) -> i64 {
        self.offset_lo
    }

    pub const fn offset_hi(&self) -> i64 {
        self.offset_hi
    }

    pub const fn is_exact_offset(&self) -> bool {
        self.exact_offset
    }

    pub fn terms(&self) -> &[AffineAddressTerm] {
        &self.address_terms
    }

    pub fn has_exact_identity(&self) -> bool {
        self.offset_lo == self.offset_hi && (self.exact_offset || !self.address_terms.is_empty())
    }

    pub fn concrete_offset_range(&self) -> Option<(i64, i64)> {
        self.address_terms
            .is_empty()
            .then_some((self.offset_lo, self.offset_hi))
    }

    fn new(
        offset_lo: i64,
        offset_hi: i64,
        exact_offset: bool,
        address_terms: Vec<AffineAddressTerm>,
    ) -> Option<Self> {
        let address_terms = normalize_terms(address_terms)?;
        if offset_lo > offset_hi
            || (exact_offset && (offset_lo != offset_hi || !address_terms.is_empty()))
            || (!address_terms.is_empty() && offset_lo != offset_hi)
        {
            return None;
        }
        Some(Self {
            offset_lo,
            offset_hi,
            exact_offset,
            address_terms,
        })
    }
}

fn normalize_terms(terms: Vec<AffineAddressTerm>) -> Option<Vec<AffineAddressTerm>> {
    let mut normalized = BTreeMap::<ValueId, i128>::new();
    for term in terms {
        let coefficient = normalized.entry(term.value).or_default();
        *coefficient = coefficient.checked_add(i128::from(term.coefficient))?;
    }
    normalized.retain(|_, coefficient| *coefficient != 0);
    normalized
        .into_iter()
        .map(|(value, coefficient)| {
            Some(AffineAddressTerm {
                value,
                coefficient: i64::try_from(coefficient).ok()?,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn affine_terms_are_canonicalized() {
        let address = SemanticMemoryAddress::affine(
            vec![
                AffineAddressTerm {
                    value: ValueId(3),
                    coefficient: 2,
                },
                AffineAddressTerm {
                    value: ValueId(1),
                    coefficient: 4,
                },
                AffineAddressTerm {
                    value: ValueId(3),
                    coefficient: -1,
                },
            ],
            8,
        )
        .expect("canonical affine address");

        assert_eq!(
            address.terms(),
            &[
                AffineAddressTerm {
                    value: ValueId(1),
                    coefficient: 4,
                },
                AffineAddressTerm {
                    value: ValueId(3),
                    coefficient: 1,
                },
            ]
        );
        assert!(address.has_exact_identity());
        assert_eq!(address.concrete_offset_range(), None);
    }

    #[test]
    fn invalid_address_invariants_are_rejected() {
        assert!(SemanticMemoryAddress::bounded(4, 3).is_none());
        assert!(SemanticMemoryAddress::affine(Vec::new(), 4).is_none());
        assert!(
            SemanticMemoryAddress::affine(
                vec![AffineAddressTerm {
                    value: ValueId(1),
                    coefficient: 0,
                }],
                4,
            )
            .is_none()
        );
    }

    #[test]
    fn flattened_condition_json_preserves_the_existing_wire_shape() {
        let condition = crate::BackwardMemoryCondition {
            region: crate::BackwardMemoryRegion::Argument { index: 0 },
            address: SemanticMemoryAddress::affine(
                vec![AffineAddressTerm {
                    value: ValueId(7),
                    coefficient: 40,
                }],
                4,
            )
            .expect("affine address"),
            size: 2,
            evidence: crate::SemanticEvidence::exact(),
            binding: None,
            expr: "*(arg0 + 40*v7 + 4)".to_string(),
            value_expr: Some("0x4241".to_string()),
            exact_value: true,
        };

        let json = serde_json::to_value(&condition).expect("serialize condition");
        assert!(json.get("address").is_none(), "{json}");
        assert_eq!(json["offset_lo"], 4);
        assert_eq!(json["offset_hi"], 4);
        assert_eq!(json["exact_offset"], false);
        assert_eq!(json["address_terms"][0]["coefficient"], 40);

        let decoded: crate::BackwardMemoryCondition =
            serde_json::from_value(json).expect("deserialize condition");
        assert_eq!(decoded, condition);
    }

    #[test]
    fn deserialization_rejects_inconsistent_wire_evidence() {
        let invalid = serde_json::json!({
            "offset_lo": 4,
            "offset_hi": 8,
            "exact_offset": true,
            "address_terms": [],
        });

        assert!(serde_json::from_value::<SemanticMemoryAddress>(invalid).is_err());
    }
}
