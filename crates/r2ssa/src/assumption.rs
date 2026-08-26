use serde::{Deserialize, Serialize};

use crate::{PredicateId, StackAddressBase};

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AssumptionScope {
    #[default]
    Function,
    Query,
    Replay,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AssumptionProvenance {
    User,
    #[default]
    ImportedContext,
    Replay,
    Derived,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AssumptionSubject {
    Parameter {
        index: usize,
    },
    /// External selector spelling retained for diagnostics and ingress.
    ///
    /// This is not semantic identity. Preparation must resolve it through the
    /// source-owned machine context and emit an exact prepared certificate.
    Register {
        name: String,
    },
    StackSlot {
        base: StackAddressBase,
        offset: i64,
    },
    Predicate {
        predicate: PredicateId,
        block_addr: u64,
        predecessor: Option<u64>,
    },
    Target {
        addr: u64,
    },
    MemoryWindow {
        addr: u64,
        size: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AssumptionValue {
    Constant {
        value: u64,
    },
    Range {
        min: u64,
        max: u64,
    },
    FiniteSet {
        values: Vec<u64>,
    },
    EnumDomain {
        name: Option<String>,
        values: Vec<i64>,
    },
    TypeHint {
        ty: String,
    },
    Branch {
        truth: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnalysisAssumption {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    pub subject: AssumptionSubject,
    pub value: AssumptionValue,
    #[serde(default)]
    pub scope: AssumptionScope,
    #[serde(default)]
    pub provenance: AssumptionProvenance,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnalysisAssumptionConflict {
    pub assumption: AnalysisAssumption,
    pub reason: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AssumptionUsageReport {
    pub applied: Vec<AnalysisAssumption>,
    pub ignored: Vec<AnalysisAssumption>,
    pub conflicts: Vec<AnalysisAssumptionConflict>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AssumptionSet {
    #[serde(default)]
    pub items: Vec<AnalysisAssumption>,
}

impl AssumptionSet {
    pub fn new(items: Vec<AnalysisAssumption>) -> Self {
        let mut out = Self { items: Vec::new() };
        out.extend(items);
        out
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &AnalysisAssumption> {
        self.items.iter()
    }

    pub fn push(&mut self, assumption: AnalysisAssumption) {
        if let Some(existing) = self
            .items
            .iter_mut()
            .find(|item| assumption_binding_eq(item, &assumption))
        {
            merge_assumption_metadata(existing, assumption);
            return;
        }
        self.items.push(assumption);
    }

    pub fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = AnalysisAssumption>,
    {
        for assumption in iter {
            self.push(assumption);
        }
    }

    pub fn type_hints_for_parameter(&self, index: usize) -> impl Iterator<Item = &str> {
        self.items.iter().filter_map(move |assumption| {
            match (&assumption.subject, &assumption.value) {
                (
                    AssumptionSubject::Parameter { index: subject },
                    AssumptionValue::TypeHint { ty },
                ) if *subject == index => Some(ty.as_str()),
                _ => None,
            }
        })
    }

    pub fn branch_truth_for_predicate(&self, predicate: PredicateId) -> Option<bool> {
        self.items.iter().find_map(
            |assumption| match (&assumption.subject, &assumption.value) {
                (
                    AssumptionSubject::Predicate {
                        predicate: subject, ..
                    },
                    AssumptionValue::Branch { truth },
                ) if *subject == predicate => Some(*truth),
                _ => None,
            },
        )
    }
}

fn assumption_binding_eq(left: &AnalysisAssumption, right: &AnalysisAssumption) -> bool {
    left.subject == right.subject && left.value == right.value && left.scope == right.scope
}

fn assumption_provenance_rank(provenance: &AssumptionProvenance) -> u8 {
    match provenance {
        AssumptionProvenance::ImportedContext => 0,
        AssumptionProvenance::Derived => 1,
        AssumptionProvenance::Replay => 2,
        AssumptionProvenance::User => 3,
    }
}

fn merge_assumption_metadata(existing: &mut AnalysisAssumption, incoming: AnalysisAssumption) {
    if existing.id.is_none() {
        existing.id = incoming.id;
    }
    if assumption_provenance_rank(&incoming.provenance)
        > assumption_provenance_rank(&existing.provenance)
    {
        existing.provenance = incoming.provenance;
    }
}

impl AssumptionUsageReport {
    pub fn is_empty(&self) -> bool {
        self.applied.is_empty() && self.ignored.is_empty() && self.conflicts.is_empty()
    }

    pub fn mark_applied(&mut self, assumption: &AnalysisAssumption) {
        self.ignored.retain(|item| item != assumption);
        self.conflicts.retain(|item| item.assumption != *assumption);
        if !self.applied.iter().any(|item| item == assumption) {
            self.applied.push(assumption.clone());
        }
    }

    pub fn mark_ignored(&mut self, assumption: &AnalysisAssumption) {
        if self.applied.iter().any(|item| item == assumption)
            || self
                .conflicts
                .iter()
                .any(|item| item.assumption == *assumption)
        {
            return;
        }
        if !self.ignored.iter().any(|item| item == assumption) {
            self.ignored.push(assumption.clone());
        }
    }

    pub fn mark_conflict(&mut self, assumption: &AnalysisAssumption, reason: impl Into<String>) {
        self.applied.retain(|item| item != assumption);
        self.ignored.retain(|item| item != assumption);
        let reason = reason.into();
        if !self
            .conflicts
            .iter()
            .any(|item| item.assumption == *assumption && item.reason == reason)
        {
            self.conflicts.push(AnalysisAssumptionConflict {
                assumption: assumption.clone(),
                reason,
            });
        }
    }

    pub fn extend(&mut self, other: &Self) {
        for assumption in &other.applied {
            self.mark_applied(assumption);
        }
        for assumption in &other.ignored {
            self.mark_ignored(assumption);
        }
        for conflict in &other.conflicts {
            self.mark_conflict(&conflict.assumption, conflict.reason.clone());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reg_type_assumption(
        reg: &str,
        ty: &str,
        provenance: AssumptionProvenance,
    ) -> AnalysisAssumption {
        AnalysisAssumption {
            id: None,
            subject: AssumptionSubject::Register {
                name: reg.to_string(),
            },
            value: AssumptionValue::TypeHint { ty: ty.to_string() },
            scope: AssumptionScope::Function,
            provenance,
        }
    }

    #[test]
    fn assumption_set_deduplicates_same_binding_and_keeps_strongest_provenance() {
        let mut assumptions = AssumptionSet::new(vec![reg_type_assumption(
            "rdi",
            "int32_t",
            AssumptionProvenance::ImportedContext,
        )]);
        assumptions.push(reg_type_assumption(
            "rdi",
            "int32_t",
            AssumptionProvenance::User,
        ));
        assumptions.extend([
            reg_type_assumption("rsi", "size_t", AssumptionProvenance::ImportedContext),
            reg_type_assumption("rsi", "size_t", AssumptionProvenance::Derived),
        ]);

        assert_eq!(assumptions.items.len(), 2);
        assert_eq!(assumptions.items[0].provenance, AssumptionProvenance::User);
        assert_eq!(
            assumptions.items[1].provenance,
            AssumptionProvenance::Derived
        );
    }
}
