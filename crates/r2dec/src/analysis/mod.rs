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

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Default)]
pub(crate) struct UseInfo {
    pub(crate) value_ids_by_var: HashMap<SSAVar, ValueId>,
    pub(crate) ambiguous_value_vars: HashSet<SSAVar>,
    pub(crate) ambiguous_value_ids: BTreeSet<ValueId>,
    pub(crate) vars_by_value_id: BTreeMap<ValueId, SSAVar>,
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
        let conflicting_value = self
            .value_ids_by_var
            .get(var)
            .copied()
            .filter(|existing| *existing != value_id);
        let conflicting_var = self
            .vars_by_value_id
            .get(&value_id)
            .filter(|existing| *existing != var)
            .cloned();
        if self.ambiguous_value_vars.contains(var)
            || self.ambiguous_value_ids.contains(&value_id)
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
            self.invalidate_value_bindings(vars, values);
            return None;
        }
        self.value_ids_by_var.insert(var.clone(), value_id);
        self.vars_by_value_id
            .entry(value_id)
            .or_insert_with(|| var.clone());
        Some(value_id)
    }

    fn invalidate_value_bindings(
        &mut self,
        mut vars: BTreeSet<SSAVar>,
        mut values: BTreeSet<ValueId>,
    ) {
        loop {
            let prior_vars = vars.len();
            let prior_values = values.len();
            for var in vars.clone() {
                if let Some(value) = self.value_ids_by_var.get(&var).copied() {
                    values.insert(value);
                }
            }
            for value in values.clone() {
                if let Some(var) = self.vars_by_value_id.get(&value).cloned() {
                    vars.insert(var);
                }
            }
            if vars.len() == prior_vars && values.len() == prior_values {
                break;
            }
        }

        for value in &values {
            self.vars_by_value_id.remove(value);
            self.ambiguous_value_ids.insert(*value);
            self.forwarded_values_by_value.remove(value);
        }
        self.forwarded_values_by_value.retain(|_, provenance| {
            provenance
                .source_value_id
                .is_none_or(|value_id| !values.contains(&value_id))
        });
        for var in vars {
            self.value_ids_by_var.remove(&var);
            self.ambiguous_value_vars.insert(var.clone());
        }
    }

    pub(crate) fn value_id_for_var(&self, var: &SSAVar) -> Option<ValueId> {
        self.exact_value_id_for_var(var)
    }

    pub(crate) fn exact_value_id_for_var(&self, var: &SSAVar) -> Option<ValueId> {
        if self.ambiguous_value_vars.contains(var) {
            return None;
        }
        let value_id = self.value_ids_by_var.get(var).copied()?;
        if self.ambiguous_value_ids.contains(&value_id) {
            return None;
        }
        self.vars_by_value_id
            .get(&value_id)
            .filter(|stored| *stored == var)
            .map(|_| value_id)
    }

    pub(crate) fn forwarded_value_for_var(&self, var: &SSAVar) -> Option<&ValueProvenance> {
        if self.ambiguous_value_vars.contains(var) {
            return None;
        }
        // Value first, as the definition accessors do. A name can be ambiguous
        // and the guard above says so; a value cannot. Where both stores hold an
        // entry and they differ, the one keyed by identity is the one that is
        // still about this value.
        self.value_id_for_var(var)
            .and_then(|value_id| self.forwarded_values_by_value.get(&value_id))
    }
}

impl StackInfo {}
