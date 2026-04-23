use serde::{Deserialize, Serialize};

use crate::PredicateId;

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
    Register {
        name: String,
    },
    StackSlot {
        base: String,
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
        Self { items }
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &AnalysisAssumption> {
        self.items.iter()
    }

    pub fn push(&mut self, assumption: AnalysisAssumption) {
        self.items.push(assumption);
    }

    pub fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = AnalysisAssumption>,
    {
        self.items.extend(iter);
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

    pub fn type_hints_for_register<'a>(&'a self, reg: &'a str) -> impl Iterator<Item = &'a str> {
        self.items.iter().filter_map(move |assumption| {
            match (&assumption.subject, &assumption.value) {
                (AssumptionSubject::Register { name }, AssumptionValue::TypeHint { ty })
                    if name.eq_ignore_ascii_case(reg) =>
                {
                    Some(ty.as_str())
                }
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
