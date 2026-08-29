use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
#[cfg(test)]
use std::sync::OnceLock;

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

#[cfg(test)]
static EMPTY_CALLEE_FACTS: OnceLock<BTreeMap<u64, CalleeFact>> = OnceLock::new();

#[cfg(test)]
pub(crate) fn empty_callee_facts() -> &'static BTreeMap<u64, CalleeFact> {
    EMPTY_CALLEE_FACTS.get_or_init(BTreeMap::new)
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct PtrArith {
    pub(crate) base: SSAVar,
    pub(crate) index: SSAVar,
    pub(crate) element_size: u32,
    pub(crate) is_sub: bool,
}

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

/// No condition codes, for a fixture whose target states none.
#[cfg(test)]
pub(crate) fn no_flag_registers() -> &'static std::collections::HashSet<String> {
    static EMPTY: std::sync::OnceLock<std::collections::HashSet<String>> =
        std::sync::OnceLock::new();
    EMPTY.get_or_init(std::collections::HashSet::new)
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
    /// Registers that are condition codes, as this target's register file defines them.
    pub(crate) flag_regs: &'a std::collections::HashSet<String>,
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
    #[cfg(test)]
    pub(crate) value_ids_by_name: HashMap<String, ValueId>,
    #[cfg(test)]
    pub(crate) ambiguous_value_names: HashSet<String>,
    pub(crate) vars_by_value_id: BTreeMap<ValueId, SSAVar>,
    pub(crate) use_counts_by_value: BTreeMap<ValueId, usize>,
    /// Condition codes as this target's register file defines them.
    pub(crate) flag_regs: std::collections::HashSet<String>,
    pub(crate) definitions_by_value: BTreeMap<ValueId, CExpr>,
    pub(crate) producers: HashMap<String, r2ssa::SSAOp>,
    pub(crate) semantic_values_by_value: BTreeMap<ValueId, SemanticValue>,
    pub(crate) phi_sources: HashMap<String, Vec<SSAVar>>,
    pub(crate) copy_sources_by_value: BTreeMap<ValueId, ValueId>,
    pub(crate) ptr_arith_by_value: BTreeMap<ValueId, PtrArith>,
    pub(crate) condition_values: BTreeSet<ValueId>,
    pub(crate) pinned: HashSet<String>,
    pub(crate) call_result_exprs: BTreeMap<(u64, usize), CExpr>,
    pub(crate) call_result_source_by_value: BTreeMap<ValueId, (u64, usize)>,
    pub(crate) switch_selector_roots: BTreeMap<u64, SemanticValue>,
    pub(crate) stack_slots_by_value: BTreeMap<ValueId, StackSlotProvenance>,
    pub(crate) stable_stack_values: HashMap<i64, SemanticValue>,
    pub(crate) stable_memory_values_by_value: BTreeMap<ValueId, SemanticValue>,
    pub(crate) forwarded_values_by_value: BTreeMap<ValueId, ValueProvenance>,
    /// Writes that reached the string-keyed half and not the value-keyed one.
    ///
    /// Every paired store is written through one helper, so the two halves
    /// cannot drift by a missed call site. They still drift when the value has
    /// no canonical identity to key on: the helper writes the name and skips the
    /// `ValueId`. Those entries are exactly what the location model has to
    /// account for before the string-keyed half can be derived rather than
    /// stored, so counting them measures what is left of that step instead of
    /// asserting it.
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

    pub(crate) fn with_value_id(value_id: ValueId, var: SSAVar) -> Self {
        Self {
            value_id: Some(value_id),
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub(crate) enum StackSlotValueKind {
    Scalar,
    AddressLike,
    #[default]
    Unknown,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct StackSlotProvenance {
    pub(crate) offset: i64,
    pub(crate) predicate_carrier: bool,
    pub(crate) return_carrier: bool,
    pub(crate) value_kind: StackSlotValueKind,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ValueProvenance {
    pub(crate) source: String,
    pub(crate) source_value_id: Option<ValueId>,
    pub(crate) source_var: Option<SSAVar>,
    pub(crate) stack_slot: Option<i64>,
}

impl StackSlotProvenance {
    #[cfg(test)]
    pub(crate) fn new(offset: i64) -> Self {
        Self {
            offset,
            predicate_carrier: false,
            return_carrier: false,
            value_kind: StackSlotValueKind::Unknown,
        }
    }

    pub(crate) fn merge(self, other: Self) -> Self {
        if self.offset != other.offset {
            return self;
        }
        Self {
            offset: self.offset,
            predicate_carrier: self.predicate_carrier || other.predicate_carrier,
            return_carrier: self.return_carrier || other.return_carrier,
            value_kind: match (self.value_kind, other.value_kind) {
                (StackSlotValueKind::Unknown, kind) | (kind, StackSlotValueKind::Unknown) => kind,
                (lhs, rhs) if lhs == rhs => lhs,
                _ => StackSlotValueKind::Unknown,
            },
        }
    }
}

fn value_ref_references_any(value: &ValueRef, ids: &BTreeSet<ValueId>) -> bool {
    value
        .value_id
        .is_some_and(|value_id| ids.contains(&value_id))
}

fn normalized_addr_references_any(addr: &NormalizedAddr, ids: &BTreeSet<ValueId>) -> bool {
    matches!(&addr.base, BaseRef::Value(value) if value_ref_references_any(value, ids))
        || addr
            .index
            .as_ref()
            .is_some_and(|value| value_ref_references_any(value, ids))
}

fn semantic_value_references_any(value: &SemanticValue, ids: &BTreeSet<ValueId>) -> bool {
    match value {
        SemanticValue::Scalar(ScalarValue::Root(value)) => value_ref_references_any(value, ids),
        SemanticValue::Scalar(ScalarValue::Expr(_)) | SemanticValue::Unknown => false,
        SemanticValue::Address(addr) | SemanticValue::Load { addr, .. } => {
            normalized_addr_references_any(addr, ids)
        }
    }
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

        #[cfg(test)]
        {
            let display = var.display_name();
            self.bind_value_name(display, value_id);
            if var.version == 0 {
                self.bind_value_name(var.name.clone(), value_id);
            }
        }
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
            self.use_counts_by_value.remove(value);
            self.definitions_by_value.remove(value);
            self.semantic_values_by_value.remove(value);
            self.copy_sources_by_value.remove(value);
            self.ptr_arith_by_value.remove(value);
            self.condition_values.remove(value);
            self.call_result_source_by_value.remove(value);
            self.stack_slots_by_value.remove(value);
            self.stable_memory_values_by_value.remove(value);
            self.forwarded_values_by_value.remove(value);
        }
        self.copy_sources_by_value
            .retain(|dst, src| !values.contains(dst) && !values.contains(src));
        self.semantic_values_by_value
            .retain(|_, value| !semantic_value_references_any(value, &values));
        self.stable_memory_values_by_value
            .retain(|_, value| !semantic_value_references_any(value, &values));
        self.forwarded_values_by_value.retain(|_, provenance| {
            provenance
                .source_value_id
                .is_none_or(|value_id| !values.contains(&value_id))
        });
        self.switch_selector_roots
            .retain(|_, value| !semantic_value_references_any(value, &values));
        self.stable_stack_values
            .retain(|_, value| !semantic_value_references_any(value, &values));
        for var in vars {
            self.value_ids_by_var.remove(&var);
            self.ambiguous_value_vars.insert(var.clone());
            #[cfg(test)]
            {
                self.invalidate_value_name(var.display_name());
                if var.version == 0 {
                    self.invalidate_value_name(var.name);
                }
            }
        }
    }

    #[cfg(test)]
    fn invalidate_value_name(&mut self, name: String) {
        self.value_ids_by_name.remove(&name);
        self.ambiguous_value_names.insert(name);
    }

    #[cfg(test)]
    fn bind_value_name(&mut self, name: String, value_id: ValueId) {
        if self.ambiguous_value_names.contains(&name) {
            return;
        }
        if let Some(existing) = self.value_ids_by_name.get(&name).copied()
            && existing != value_id
        {
            self.value_ids_by_name.remove(&name);
            self.ambiguous_value_names.insert(name);
            return;
        }
        self.value_ids_by_name.insert(name, value_id);
    }

    pub(crate) fn note_use_for_var(&mut self, var: &SSAVar) {
        if let Some(value_id) = self.exact_value_id_for_var(var) {
            *self.use_counts_by_value.entry(value_id).or_insert(0) += 1;
        } else {
            self.dropped_unkeyed_fact.get_or_insert("use_counts");
        }
    }

    pub(crate) fn note_condition_var(&mut self, var: &SSAVar) {
        if let Some(value_id) = self.exact_value_id_for_var(var) {
            self.condition_values.insert(value_id);
        } else {
            self.dropped_unkeyed_fact.get_or_insert("condition_vars");
        }
    }

    #[cfg(test)]
    pub(crate) fn insert_stack_slot_for_name(&mut self, name: &str, slot: StackSlotProvenance) {
        if let Some(value_id) = self.value_id_for_name_or_bind(name) {
            self.stack_slots_by_value.insert(value_id, slot);
        }
    }

    /// Record a semantic value against the exact upstream value identity.
    pub(crate) fn insert_semantic_value_for_value_if_absent(
        &mut self,
        value_id: Option<ValueId>,
        value: SemanticValue,
    ) {
        match value_id {
            Some(value_id) => {
                self.semantic_values_by_value
                    .entry(value_id)
                    .or_insert(value);
            }
            None => {
                self.dropped_unkeyed_fact.get_or_insert("semantic_values");
            }
        }
    }

    /// Resolve a spelling only when it is already bound to one exact value.
    ///
    /// Production never manufactures a `ValueId` for text: a spelling can
    /// denote a binding containing several SSA values and is not upstream
    /// evidence for any one of them. Legacy fixtures that have no SSA artifact
    /// may allocate a private synthetic identity under `cfg(test)` only.
    #[cfg(test)]
    pub(crate) fn value_id_for_name_or_bind(&mut self, name: &str) -> Option<ValueId> {
        if let Some(value_id) = self.value_id_for_name(name) {
            return Some(value_id);
        }
        if self.ambiguous_value_names.contains(name) {
            return None;
        }
        let value_id = ValueId(9500 + self.value_ids_by_name.len() as u32);
        self.bind_value_name(name.to_string(), value_id);
        self.value_id_for_name(name)
    }

    pub(crate) fn insert_call_result_source_for_value(
        &mut self,
        value: ValueId,
        source_call: (u64, usize),
    ) {
        if !self.ambiguous_value_ids.contains(&value) {
            self.call_result_source_by_value.insert(value, source_call);
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

    #[cfg(test)]
    pub(crate) fn value_id_for_name(&self, name: &str) -> Option<ValueId> {
        if self.ambiguous_value_names.contains(name) {
            return None;
        }
        self.value_ids_by_name.get(name).copied()
    }

    pub(crate) fn var_for_value_id(&self, value_id: ValueId) -> Option<&SSAVar> {
        if self.ambiguous_value_ids.contains(&value_id) {
            return None;
        }
        self.vars_by_value_id.get(&value_id)
    }

    pub(crate) fn definition_for_var(&self, var: &SSAVar) -> Option<&CExpr> {
        if self.ambiguous_value_vars.contains(var) {
            return None;
        }
        self.value_id_for_var(var)
            .and_then(|value_id| self.definitions_by_value.get(&value_id))
    }

    pub(crate) fn use_count_for_value(&self, value: ValueId) -> usize {
        if self.ambiguous_value_ids.contains(&value) {
            return 0;
        }
        self.use_counts_by_value.get(&value).copied().unwrap_or(0)
    }

    pub(crate) fn semantic_value_for_var(&self, var: &SSAVar) -> Option<&SemanticValue> {
        if self.ambiguous_value_vars.contains(var) {
            return None;
        }
        self.value_id_for_var(var)
            .and_then(|value_id| self.semantic_values_by_value.get(&value_id))
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

    /// File a definition against the value a spelling names, if it has none.
    #[cfg(test)]
    pub(crate) fn insert_definition_for_name_if_absent(&mut self, name: &str, expr: CExpr) {
        match self.value_id_for_name_or_bind(name) {
            Some(value_id) => {
                self.definitions_by_value.entry(value_id).or_insert(expr);
            }
            None => {
                self.dropped_unkeyed_fact.get_or_insert("definitions");
            }
        }
    }

    pub(crate) fn ptr_arith_for_var(&self, var: &SSAVar) -> Option<&PtrArith> {
        if self.ambiguous_value_vars.contains(var) {
            return None;
        }
        self.value_id_for_var(var)
            .and_then(|value_id| self.ptr_arith_by_value.get(&value_id))
    }

    pub(crate) fn is_condition_value(&self, value: ValueId) -> bool {
        if self.ambiguous_value_ids.contains(&value) {
            return false;
        }
        self.condition_values.contains(&value)
    }
}

impl StackInfo {}
