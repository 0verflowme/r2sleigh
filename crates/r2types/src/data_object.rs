use std::collections::BTreeMap;

use crate::{CTypeLike, ExternalAggregateKind, ExternalTypeDb, parse_c_type_like};

/// The owner that supplied a program data object's type.
///
/// This is deliberately not machine evidence. A renderer may trust it because
/// the source marked the analysis fact, but its proof line must say so.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum DataObjectTypeProvenance {
    Radare2,
}

/// One accepted type, keyed outside this value by the object's address.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub struct DataObjectTypeFact {
    pub ty: CTypeLike,
    pub provenance: DataObjectTypeProvenance,
}

/// Why a source observation did not become a renderer type.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub enum DataObjectTypeRefusal {
    /// radare2 named the object but had no address-linked type for it.
    MissingSourceType,
    /// The parser could not turn the spelling into a type declared by the
    /// current source type context.
    UnplaceableSourceType(String),
    /// Two source observations for one structural address disagreed. Neither
    /// is allowed to win by observation order.
    ConflictingSourceTypes { first: CTypeLike, second: CTypeLike },
}

/// Program-scope data object types and the refusals that prevented a type.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProgramDataObjectTypeFacts {
    accepted: BTreeMap<u64, DataObjectTypeFact>,
    refused: BTreeMap<u64, DataObjectTypeRefusal>,
}

impl ProgramDataObjectTypeFacts {
    /// Parse one function snapshot's radare2 observations without minting
    /// typedefs that its type database cannot place.
    pub fn from_radare2<'a>(
        observations: impl IntoIterator<Item = (u64, Option<&'a str>)>,
        ptr_bits: u32,
        type_db: &ExternalTypeDb,
    ) -> Self {
        let mut facts = Self::default();
        for (address, spelling) in observations {
            match spelling {
                None => {
                    facts.observe_refused(address, DataObjectTypeRefusal::MissingSourceType);
                }
                Some(spelling) => {
                    match parse_placeable_data_object_type(spelling, ptr_bits, type_db) {
                        Some(ty) => facts.observe_accepted(address, ty),
                        None => {
                            facts.observe_refused(
                                address,
                                DataObjectTypeRefusal::UnplaceableSourceType(spelling.to_string()),
                            );
                        }
                    }
                }
            }
        }
        facts
    }

    pub fn accepted(&self) -> &BTreeMap<u64, DataObjectTypeFact> {
        &self.accepted
    }

    pub fn refused(&self) -> &BTreeMap<u64, DataObjectTypeRefusal> {
        &self.refused
    }

    pub fn get(&self, address: u64) -> Option<&DataObjectTypeFact> {
        self.accepted.get(&address)
    }

    /// Merge another function's observations into the program view.
    ///
    /// Absence and an unplaceable spelling cannot displace an accepted fact.
    /// Two different accepted types are a conflict and remove the type, so
    /// traversal order cannot decide rendered C.
    pub fn absorb(&mut self, other: &Self) {
        for (&address, refusal) in &other.refused {
            if !self.accepted.contains_key(&address) {
                self.observe_refused(address, refusal.clone());
            }
        }
        for (&address, fact) in &other.accepted {
            self.observe_accepted(address, fact.ty.clone());
        }
    }

    fn observe_accepted(&mut self, address: u64, ty: CTypeLike) {
        match self.accepted.get(&address) {
            Some(existing) if existing.ty == ty => {}
            Some(existing) => {
                let existing = existing.ty.clone();
                let (first, second) = if existing <= ty {
                    (existing, ty)
                } else {
                    (ty, existing)
                };
                self.accepted.remove(&address);
                self.refused.insert(
                    address,
                    DataObjectTypeRefusal::ConflictingSourceTypes { first, second },
                );
            }
            None if matches!(
                self.refused.get(&address),
                Some(DataObjectTypeRefusal::ConflictingSourceTypes { .. })
            ) => {}
            None => {
                self.refused.remove(&address);
                self.accepted.insert(
                    address,
                    DataObjectTypeFact {
                        ty,
                        provenance: DataObjectTypeProvenance::Radare2,
                    },
                );
            }
        }
    }

    fn observe_refused(&mut self, address: u64, refusal: DataObjectTypeRefusal) {
        if self.accepted.contains_key(&address) {
            return;
        }
        match self.refused.entry(address) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(refusal);
            }
            std::collections::btree_map::Entry::Occupied(mut entry)
                if refusal < *entry.get()
                    && !matches!(
                        entry.get(),
                        DataObjectTypeRefusal::ConflictingSourceTypes { .. }
                    ) =>
            {
                entry.insert(refusal);
            }
            std::collections::btree_map::Entry::Occupied(_) => {}
        }
    }
}

fn parse_placeable_data_object_type(
    spelling: &str,
    ptr_bits: u32,
    type_db: &ExternalTypeDb,
) -> Option<CTypeLike> {
    let ty = parse_c_type_like(spelling, ptr_bits)?;
    data_object_type_is_placeable(&ty, type_db, false).then_some(ty)
}

fn data_object_type_is_placeable(
    ty: &CTypeLike,
    type_db: &ExternalTypeDb,
    behind_pointer: bool,
) -> bool {
    match ty {
        CTypeLike::Void => behind_pointer,
        CTypeLike::Bool | CTypeLike::Int { .. } | CTypeLike::Float(_) | CTypeLike::BitVector(_) => {
            true
        }
        CTypeLike::Pointer(inner) => data_object_type_is_placeable(inner, type_db, true),
        CTypeLike::Array(inner, _) => data_object_type_is_placeable(inner, type_db, false),
        CTypeLike::Struct(name) => {
            type_db.resolve_aggregate_kind(name) == Some(ExternalAggregateKind::Struct)
        }
        CTypeLike::Union(name) => {
            type_db.resolve_aggregate_kind(name) == Some(ExternalAggregateKind::Union)
        }
        CTypeLike::Enum(name) => {
            type_db.resolve_aggregate_kind(name) == Some(ExternalAggregateKind::Enum)
        }
        CTypeLike::Typedef(name) => type_db.declares_typedef(name),
        CTypeLike::Function { .. } | CTypeLike::Unknown => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_builtin_radare_type_is_accepted_and_marked() {
        let facts = ProgramDataObjectTypeFacts::from_radare2(
            [(0x7000, Some("int32_t"))],
            64,
            &ExternalTypeDb::default(),
        );
        assert_eq!(
            facts.get(0x7000).map(|fact| &fact.ty),
            Some(&CTypeLike::i32())
        );
        assert_eq!(
            facts.get(0x7000).map(|fact| fact.provenance),
            Some(DataObjectTypeProvenance::Radare2)
        );
    }

    #[test]
    fn an_undeclared_typedef_spelling_is_refused() {
        let facts = ProgramDataObjectTypeFacts::from_radare2(
            [(0x7000, Some("looks_specific_t"))],
            64,
            &ExternalTypeDb::default(),
        );
        assert!(facts.get(0x7000).is_none());
        assert_eq!(
            facts.refused().get(&0x7000),
            Some(&DataObjectTypeRefusal::UnplaceableSourceType(
                "looks_specific_t".to_string()
            ))
        );
    }

    #[test]
    fn no_radare_type_is_a_refusal_not_a_default_type() {
        let facts = ProgramDataObjectTypeFacts::from_radare2(
            [(0x7000, None)],
            64,
            &ExternalTypeDb::default(),
        );
        assert!(facts.get(0x7000).is_none());
        assert_eq!(
            facts.refused().get(&0x7000),
            Some(&DataObjectTypeRefusal::MissingSourceType)
        );
    }

    #[test]
    fn accepted_program_fact_survives_a_later_missing_observation() {
        let mut accepted = ProgramDataObjectTypeFacts::from_radare2(
            [(0x7000, Some("int32_t"))],
            64,
            &ExternalTypeDb::default(),
        );
        let missing = ProgramDataObjectTypeFacts::from_radare2(
            [(0x7000, None)],
            64,
            &ExternalTypeDb::default(),
        );
        accepted.absorb(&missing);
        assert_eq!(
            accepted.get(0x7000).map(|fact| &fact.ty),
            Some(&CTypeLike::i32())
        );
    }

    #[test]
    fn conflicting_program_types_refuse_independent_of_order() {
        let signed = ProgramDataObjectTypeFacts::from_radare2(
            [(0x7000, Some("int32_t"))],
            64,
            &ExternalTypeDb::default(),
        );
        let unsigned = ProgramDataObjectTypeFacts::from_radare2(
            [(0x7000, Some("uint32_t"))],
            64,
            &ExternalTypeDb::default(),
        );
        for (mut first, second) in [(signed.clone(), unsigned.clone()), (unsigned, signed)] {
            first.absorb(&second);
            assert!(first.get(0x7000).is_none());
            assert!(matches!(
                first.refused().get(&0x7000),
                Some(DataObjectTypeRefusal::ConflictingSourceTypes { .. })
            ));
        }
    }
}
