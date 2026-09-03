//! What aliases what, asked of the machine rather than of a table of names.
//!
//! Three tables in this crate used to answer register-identity questions by
//! matching spellings: whether two names are the same parameter, which family
//! a name belongs to, and whether a name is a frame or stack pointer. Each was
//! written per architecture and each was wrong somewhere, because a name is
//! not what makes two registers the same storage -- geometry is. `rdx` and
//! `dh` share a spelling family and no bytes; `ah` and `al` are one byte each
//! of the same register and not the same byte.
//!
//! This asks the prepared function's own machine context instead. Every
//! register it declares carries a `CanonicalStorageId`, and that is the
//! identity the rest of the pipeline already keys on.

use std::collections::BTreeMap;

use r2ssa::{CanonicalStorageId, CanonicalStorageSpace, RegisterFamilyInfo, RegisterFamilySlot};

/// Register identity for one prepared function, derived from its machine
/// context. Empty when the machine context declares no registers, in which
/// case every question falls back to comparing the names as given.
#[derive(Debug, Clone, Default)]
pub struct RegisterIdentity {
    families: RegisterFamilyInfo,
    storage_by_name: BTreeMap<String, CanonicalStorageId>,
}

impl RegisterIdentity {
    pub fn from_prepared(prepared: &r2ssa::SsaArtifact) -> Self {
        Self::from_register_storages(prepared.machine_context().register_storages_by_name())
    }

    pub fn from_register_storages(storages: &BTreeMap<String, CanonicalStorageId>) -> Self {
        let storage_by_name: BTreeMap<String, CanonicalStorageId> = storages
            .iter()
            .filter(|(_, storage)| storage.space == CanonicalStorageSpace::Register)
            .map(|(name, storage)| (name.trim().to_ascii_lowercase(), *storage))
            .collect();
        let families = RegisterFamilyInfo::from_register_storages(
            storage_by_name
                .iter()
                .map(|(name, storage)| (name.as_str(), storage.offset, storage.size)),
        );
        Self {
            families,
            storage_by_name,
        }
    }

    /// Whether the machine context named any register at all.
    pub fn is_empty(&self) -> bool {
        self.storage_by_name.is_empty()
    }

    pub fn storage_of(&self, name: &str) -> Option<CanonicalStorageId> {
        self.storage_by_name
            .get(name.trim().to_ascii_lowercase().as_str())
            .copied()
    }

    /// The canonical identity of the register a name belongs to: the widest
    /// storage containing it, which every alias of it shares.
    pub fn family_slot(&self, name: &str) -> Option<RegisterFamilySlot> {
        self.families
            .widest_slot_for_name(name.trim().to_ascii_lowercase().as_str())
    }

    /// Whether two register names carry the same ABI parameter.
    ///
    /// A parameter passed in `rdx` is read back as `rdx`, `edx`, `dx` or `dl`
    /// -- every one of them starting at the register's own offset. It is never
    /// read as `dh`, which starts one byte in and holds different bits. So the
    /// question is not "same family", which `dh` also answers yes to, but
    /// "same storage origin": the same space, at the same offset.
    ///
    /// Names the machine context does not declare fall back to comparing the
    /// spellings, which is all that is known about them.
    pub fn same_parameter_storage(&self, expected: &str, actual: &str) -> bool {
        if expected.eq_ignore_ascii_case(actual) {
            return true;
        }
        match (self.storage_of(expected), self.storage_of(actual)) {
            (Some(expected), Some(actual)) => {
                expected.space == actual.space && expected.offset == actual.offset
            }
            _ => false,
        }
    }
}
