#[cfg(test)]
use std::collections::{BTreeMap, BTreeSet};

#[cfg(test)]
use r2ssa::{ObjectId, ValueId};

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct CallSiteId {
    pub(crate) block_addr: u64,
    pub(crate) op_idx: usize,
}

#[cfg(test)]
impl From<(u64, usize)> for CallSiteId {
    fn from((block_addr, op_idx): (u64, usize)) -> Self {
        Self { block_addr, op_idx }
    }
}

#[cfg(test)]
impl From<CallSiteId> for (u64, usize) {
    fn from(value: CallSiteId) -> Self {
        (value.block_addr, value.op_idx)
    }
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CallOwnerKind {
    StableLocal,
}

/// The exact upstream identity that owns one call result.
///
/// A rendered symbol is deliberately absent: one binding can carry several
/// SSA values over its lifetime, and its presentation spelling cannot say
/// which result a particular occurrence came from.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum CallOwnerIdentity {
    Value(ValueId),
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallOwner {
    pub(crate) identity: CallOwnerIdentity,
    pub(crate) kind: CallOwnerKind,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallOwnershipFact {
    pub(crate) source: CallSiteId,
    pub(crate) owner: Option<CallOwner>,
    pub(crate) aliases: BTreeSet<ValueId>,
    pub(crate) direct_aliases: BTreeSet<ValueId>,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Default)]
pub(crate) struct SemanticOwnershipFacts {
    pub(crate) call_ownership: BTreeMap<CallSiteId, CallOwnershipFact>,
    pub(crate) value_sources: BTreeMap<ValueId, CallSiteId>,
    pub(crate) object_sources: BTreeMap<ObjectId, CallSiteId>,
}

#[cfg(not(test))]
#[derive(Debug, Clone, PartialEq, Default)]
pub(crate) struct SemanticOwnershipFacts;
