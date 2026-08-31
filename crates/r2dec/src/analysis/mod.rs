use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use r2ssa::{FunctionSSABlock, SSAVar, ValueId};
use r2types::{CalleeFact, CalleeResolutionFacts, InterprocSummaryView, TypeOracle};

use crate::ast::CExpr;

pub(crate) type SSABlock = FunctionSSABlock;

pub(crate) mod lower;
pub(crate) mod prepared_semantic;
pub(crate) mod utils;

pub(crate) use prepared_semantic::{
    PreparedCallView, PreparedRuntimeFactsError, PreparedSemanticView, PreparedSemanticViewInputs,
    build_prepared_runtime_facts_with_control,
};

#[allow(dead_code)]
#[derive(Debug, Clone, Default)]
pub(crate) struct DecompilerFacts {
    pub(crate) use_info: UseInfo,
    pub(crate) stack_info: StackInfo,
}

impl DecompilerFacts {
    pub(crate) fn semantic(&self) -> &UseInfo {
        &self.use_info
    }
}

#[allow(dead_code)]
#[derive(Clone)]

pub(crate) struct PassEnv<'a> {
    /// The one renderer projection from BindingId to SymbolId. Analysis only
    /// borrows it while translating exact ValueIds into references.
    pub(crate) binding_names: Option<&'a crate::binding_plan::BindingNameResolution>,
    pub(crate) ptr_size: u32,
    pub(crate) sp_name: &'a str,
    pub(crate) fp_name: &'a str,
    pub(crate) ret_reg_name: &'a str,
    #[cfg(test)]
    pub(crate) function_names: &'a HashMap<u64, String>,
    #[cfg(test)]
    pub(crate) strings: &'a HashMap<u64, String>,
    /// What the binary calls the thing at an address, which is not a name this
    /// rendering declares.
    #[cfg(test)]
    pub(crate) binary_symbols: &'a HashMap<u64, String>,
    /// String literals the source recorded, for rendering a constant that
    /// points at text as the text it points at.
    pub(crate) string_literals: &'a BTreeMap<u64, String>,
    pub(crate) callee_facts: &'a BTreeMap<u64, CalleeFact>,
    pub(crate) callee_resolution: Option<&'a CalleeResolutionFacts>,
    pub(crate) summary_view: Option<&'a InterprocSummaryView>,
    pub(crate) arg_regs: &'a [String],
    /// Where a rendered name is written down, so building a reference can mint one.
    pub(crate) symbols: &'a std::cell::RefCell<crate::symbol::SymbolTable>,
    pub(crate) caller_saved_regs: &'a HashSet<String>,
    pub(crate) type_oracle: Option<&'a dyn TypeOracle>,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub(crate) struct UseInfo {
    identities: ExactValueIdentities,
    pub(crate) pinned: HashSet<String>,
    pub(crate) call_result_exprs: BTreeMap<(u64, usize), CExpr>,
    pub(crate) forwarded_values_by_value: BTreeMap<ValueId, ValueProvenance>,
    /// The first fact dropped because its variable had no exact value identity.
    ///
    /// Each writer below keys its fact by `ValueId`, and where the variable has
    /// no exact one the fact used to be counted here and thrown away. Counting
    /// a dropped fact is not accounting for it: the analysis then carries on
    /// with a table that is missing something, and nothing downstream can tell.
    ///
    /// It is measured at zero on every corpus configuration, so recording the
    /// first one and refusing costs nothing and stops the silent loss.
    pub(crate) dropped_unkeyed_fact: Option<&'static str>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ValueRef {
    pub(crate) value_id: Option<ValueId>,
    pub(crate) var: SSAVar,
}

impl ValueRef {
    pub(crate) fn new(var: SSAVar) -> Self {
        Self {
            value_id: None,
            var,
        }
    }

    #[allow(dead_code)]
    pub(crate) fn value_id(&self) -> Option<ValueId> {
        self.value_id
    }
}

impl From<SSAVar> for ValueRef {
    fn from(var: SSAVar) -> Self {
        Self::new(var)
    }
}

impl From<&SSAVar> for ValueRef {
    fn from(var: &SSAVar) -> Self {
        Self::new(var.clone())
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BaseRef {
    Value(ValueRef),
    StackSlot(i64),
    Raw(CExpr),
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct NormalizedAddr {
    pub(crate) base: BaseRef,
    pub(crate) index: Option<ValueRef>,
    pub(crate) scale_bytes: i64,
    pub(crate) offset_bytes: i64,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum ScalarValue {
    Root(ValueRef),
    Expr(CExpr),
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum SemanticValue {
    Scalar(ScalarValue),
    Address(NormalizedAddr),
    Load {
        space: r2il::SpaceId,
        addr: NormalizedAddr,
        size: u32,
    },
    Unknown,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct FrameSlotMergeSummary {
    pub(crate) slot_offset: i64,
    pub(crate) merge_block_addr: u64,
    pub(crate) load_name: String,
    pub(crate) incoming: BTreeMap<u64, SemanticValue>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct FrameObjectFieldKey {
    pub(crate) base_slot_offset: i64,
    pub(crate) field_offset: i64,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Default)]
pub(crate) struct StackInfo {
    pub(crate) stack_vars: HashMap<i64, String>,
    pub(crate) definition_overrides: HashMap<String, CExpr>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ValueProvenance {
    pub(crate) source: String,
    pub(crate) source_value_id: Option<ValueId>,
    pub(crate) source_var: Option<SSAVar>,
    pub(crate) stack_slot: Option<i64>,
}

impl UseInfo {
    pub(crate) fn bind_value_id(&mut self, var: &SSAVar, value_id: ValueId) -> Option<ValueId> {
        match self.identities.bind(var, value_id) {
            Bind::Bound(value_id) => Some(value_id),
            Bind::Poisoned(values) => {
                // The forwarding table is keyed by the same values, so a value
                // that just lost its exact identity must lose its provenance
                // with it -- both the entry for the value and any entry that
                // names it as a source.
                for value in &values {
                    self.forwarded_values_by_value.remove(value);
                }
                self.forwarded_values_by_value.retain(|_, provenance| {
                    provenance
                        .source_value_id
                        .is_none_or(|value_id| !values.contains(&value_id))
                });
                None
            }
        }
    }

    pub(crate) fn value_id_for_var(&self, var: &SSAVar) -> Option<ValueId> {
        self.exact_value_id_for_var(var)
    }

    pub(crate) fn exact_value_id_for_var(&self, var: &SSAVar) -> Option<ValueId> {
        self.identities.value_for_var(var)
    }

    pub(crate) fn forwarded_value_for_var(&self, var: &SSAVar) -> Option<&ValueProvenance> {
        // Value first, as the definition accessors do. A name can be ambiguous
        // and the identity relation says so; a value cannot. Where both stores
        // hold an entry and they differ, the one keyed by identity is the one
        // that is still about this value.
        self.value_id_for_var(var)
            .and_then(|value_id| self.forwarded_values_by_value.get(&value_id))
    }
}

/// What a `bind` did.
pub(crate) enum Bind {
    /// The pair was exact and is now recorded.
    Bound(ValueId),
    /// The pair contradicted something already known, so every value in the
    /// contradicted component is now poisoned. Callers holding tables keyed by
    /// `ValueId` must drop these.
    Poisoned(BTreeSet<ValueId>),
}

/// The exact one-to-one correspondence between a presentation variable and the
/// value it names.
///
/// This is one relation, so it is one field. `by_value` is the stored
/// direction, keyed by the identity the rest of the model uses. `by_var` is an
/// index over the same pairs, and `poisoned_vars` is an index over
/// `poisoned_values`; both exist because `UseInfo`'s accessors are asked
/// questions in both directions and the project's own asymptotics rule says a
/// lookup is not a scan. Neither is separately writable: `bind` is the only
/// mutator, and it maintains all four together.
///
/// That is the whole point of the type. These were four `pub(crate)` fields of
/// `UseInfo`, so a caller could read one direction, act on it, and be
/// contradicted by the other -- one fact keyed several ways, each independently
/// writable, which is the shape this rewrite exists to remove.
///
/// A contradicted pair is not repaired, it is poisoned. Both halves are removed
/// and recorded, so a later `bind` of either half fails rather than re-creating
/// a binding already proven ambiguous, and the poison spreads to the whole
/// connected component rather than to the two names that happened to collide.
#[derive(Debug, Clone, PartialEq, Default)]
pub(crate) struct ExactValueIdentities {
    by_value: BTreeMap<ValueId, SSAVar>,
    by_var: HashMap<SSAVar, ValueId>,
    poisoned_values: BTreeSet<ValueId>,
    poisoned_vars: HashSet<SSAVar>,
}

impl ExactValueIdentities {
    pub(crate) fn bind(&mut self, var: &SSAVar, value_id: ValueId) -> Bind {
        let conflicting_value = self
            .by_var
            .get(var)
            .copied()
            .filter(|existing| *existing != value_id);
        let conflicting_var = self
            .by_value
            .get(&value_id)
            .filter(|existing| *existing != var)
            .cloned();
        if self.poisoned_vars.contains(var)
            || self.poisoned_values.contains(&value_id)
            || conflicting_value.is_some()
            || conflicting_var.is_some()
        {
            let mut vars = BTreeSet::from([var.clone()]);
            if let Some(conflicting_var) = conflicting_var {
                vars.insert(conflicting_var);
            }
            let mut values = BTreeSet::from([value_id]);
            if let Some(conflicting_value) = conflicting_value {
                values.insert(conflicting_value);
            }
            return Bind::Poisoned(self.poison(vars, values));
        }
        self.by_var.insert(var.clone(), value_id);
        self.by_value.insert(value_id, var.clone());
        Bind::Bound(value_id)
    }

    /// The value this variable exactly names, if the pair is mutual and neither
    /// half is poisoned.
    pub(crate) fn value_for_var(&self, var: &SSAVar) -> Option<ValueId> {
        if self.poisoned_vars.contains(var) {
            return None;
        }
        let value_id = self.by_var.get(var).copied()?;
        if self.poisoned_values.contains(&value_id) {
            return None;
        }
        self.by_value
            .get(&value_id)
            .filter(|stored| *stored == var)
            .map(|_| value_id)
    }

    /// Poison a contradicted component and return the values it covered.
    ///
    /// A contradiction is transitive: if two variables claim one value, every
    /// value either of them claims is equally unproven, and so on. The fixpoint
    /// closes over both directions before anything is removed.
    fn poison(
        &mut self,
        mut vars: BTreeSet<SSAVar>,
        mut values: BTreeSet<ValueId>,
    ) -> BTreeSet<ValueId> {
        loop {
            let prior_vars = vars.len();
            let prior_values = values.len();
            for var in vars.clone() {
                if let Some(value) = self.by_var.get(&var).copied() {
                    values.insert(value);
                }
            }
            for value in values.clone() {
                if let Some(var) = self.by_value.get(&value).cloned() {
                    vars.insert(var);
                }
            }
            if vars.len() == prior_vars && values.len() == prior_values {
                break;
            }
        }

        for value in &values {
            self.by_value.remove(value);
            self.poisoned_values.insert(*value);
        }
        for var in vars {
            self.by_var.remove(&var);
            self.poisoned_vars.insert(var);
        }
        values
    }

    /// Whether the two directions still describe the same set of pairs.
    ///
    /// They can only disagree if something other than `bind` wrote one of them,
    /// which the privacy of the fields is what prevents. Asserted in tests
    /// rather than trusted.
    #[cfg(test)]
    pub(crate) fn directions_agree(&self) -> bool {
        self.by_var.len() == self.by_value.len()
            && self
                .by_var
                .iter()
                .all(|(var, value)| self.by_value.get(value) == Some(var))
    }
}

impl StackInfo {}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> SSAVar {
        SSAVar::new(name, 1, 8)
    }

    #[test]
    fn exact_identities_keep_both_directions_in_step() {
        let mut identities = ExactValueIdentities::default();
        for (name, value) in [("a", 1u32), ("b", 2), ("c", 3)] {
            assert!(matches!(
                identities.bind(&var(name), ValueId(value)),
                Bind::Bound(_)
            ));
        }

        assert!(identities.directions_agree());
        assert_eq!(identities.value_for_var(&var("b")), Some(ValueId(2)));
    }

    #[test]
    fn a_contradicted_pair_poisons_its_whole_component() {
        let mut identities = ExactValueIdentities::default();
        assert!(matches!(
            identities.bind(&var("a"), ValueId(1)),
            Bind::Bound(_)
        ));
        assert!(matches!(
            identities.bind(&var("b"), ValueId(2)),
            Bind::Bound(_)
        ));

        // `a` already names 1 and 2 already belongs to `b`, so neither pair is
        // proven any more and the poison must reach `b` and 1 as well as the
        // two halves that collided.
        let Bind::Poisoned(values) = identities.bind(&var("a"), ValueId(2)) else {
            panic!("a second value for one variable must poison the component");
        };
        assert_eq!(values, BTreeSet::from([ValueId(1), ValueId(2)]));

        assert_eq!(identities.value_for_var(&var("a")), None);
        assert_eq!(identities.value_for_var(&var("b")), None);
        assert!(identities.directions_agree());
    }

    #[test]
    fn poisoning_is_sticky_against_a_later_rebind() {
        let mut identities = ExactValueIdentities::default();
        identities.bind(&var("a"), ValueId(1));
        identities.bind(&var("b"), ValueId(1));

        // Re-asserting the original pair must not resurrect it: it was proven
        // ambiguous, and forgetting that is how a wrong name reaches the output.
        assert!(matches!(
            identities.bind(&var("a"), ValueId(1)),
            Bind::Poisoned(_)
        ));
        assert_eq!(identities.value_for_var(&var("a")), None);
        assert!(identities.directions_agree());
    }
}
