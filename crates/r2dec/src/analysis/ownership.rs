use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct CallSiteId {
    pub(crate) block_addr: u64,
    pub(crate) op_idx: usize,
}

impl From<(u64, usize)> for CallSiteId {
    fn from((block_addr, op_idx): (u64, usize)) -> Self {
        Self { block_addr, op_idx }
    }
}

impl From<CallSiteId> for (u64, usize) {
    fn from(value: CallSiteId) -> Self {
        (value.block_addr, value.op_idx)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CallOwnerKind {
    StableLocal,
    StableStackLocal,
    Parameter,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallOwner {
    pub(crate) visible_name: String,
    pub(crate) kind: CallOwnerKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallOwnershipFact {
    pub(crate) source: CallSiteId,
    pub(crate) owner: Option<CallOwner>,
    pub(crate) aliases: BTreeSet<String>,
    pub(crate) direct_aliases: BTreeSet<String>,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub(crate) struct SemanticOwnershipFacts {
    pub(crate) call_ownership: BTreeMap<CallSiteId, CallOwnershipFact>,
    pub(crate) alias_sources: HashMap<String, CallSiteId>,
    pub(crate) visible_owner_sources: HashMap<String, CallSiteId>,
    pub(crate) visible_owned_names: BTreeSet<String>,
}

impl SemanticOwnershipFacts {
    pub(crate) fn ownership_for_source(&self, source: CallSiteId) -> Option<&CallOwnershipFact> {
        self.call_ownership.get(&source)
    }

    pub(crate) fn source_for_alias(&self, alias: &str) -> Option<CallSiteId> {
        self.alias_sources
            .get(alias)
            .copied()
            .or_else(|| self.alias_sources.get(&alias.to_ascii_lowercase()).copied())
    }

    pub(crate) fn source_for_visible_owner_name(&self, name: &str) -> Option<CallSiteId> {
        self.visible_owner_sources.get(name).copied().or_else(|| {
            self.visible_owner_sources
                .get(&name.to_ascii_lowercase())
                .copied()
        })
    }

    pub(crate) fn has_visible_owner_name(&self, name: &str) -> bool {
        self.visible_owned_names
            .contains(&name.to_ascii_lowercase())
    }
}
