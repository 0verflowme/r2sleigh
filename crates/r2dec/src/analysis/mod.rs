use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
#[cfg(test)]
use std::sync::OnceLock;

use r2ssa::{FunctionSSABlock, SSAVar, ValueId};
use r2types::{CalleeFact, CalleeResolutionFacts, InterprocSummaryView, TypeOracle};

use crate::ast::CExpr;

pub(crate) type SSABlock = FunctionSSABlock;

// Pass dependency invariant:
// UseInfo -> (FlagInfo, StackInfo) -> PredicateSimplifier -> statement emit.
pub(crate) mod lower;
pub(crate) mod ownership;
pub(crate) mod predicate;
pub(crate) mod prepared_semantic;
pub(crate) mod utils;

#[cfg(test)]
pub(crate) use ownership::{CallOwner, CallOwnerKind, CallOwnershipFact, CallSiteId};
pub(crate) use ownership::SemanticOwnershipFacts;
pub(crate) use predicate::{PredicateAnalysisView, PredicateSimplifier};
pub(crate) use prepared_semantic::{
    PreparedCallView, PreparedRuntimeFactsError, PreparedSemanticView,
    PreparedSemanticViewInputs,
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
    pub(crate) ownership: SemanticOwnershipFacts,
    pub(crate) flag_info: FlagInfo,
    pub(crate) stack_info: StackInfo,
}

impl DecompilerFacts {
    pub(crate) fn semantic(&self) -> &UseInfo {
        &self.use_info
    }

    pub(crate) fn flags(&self) -> &FlagInfo {
        &self.flag_info
    }

    pub(crate) fn stack(&self) -> &StackInfo {
        &self.stack_info
    }

}

/// No condition codes, for a fixture whose target states none.
#[cfg(test)]
pub(crate) fn no_flag_registers() -> &'static std::collections::HashSet<String> {
    static EMPTY: std::sync::OnceLock<std::collections::HashSet<String>> =
        std::sync::OnceLock::new();
    EMPTY.get_or_init(std::collections::HashSet::new)
}

#[cfg(test)]
pub(crate) fn no_carrier_aliases() -> &'static HashMap<String, String> {
    static EMPTY: std::sync::OnceLock<HashMap<String, String>> = std::sync::OnceLock::new();
    EMPTY.get_or_init(HashMap::new)
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
    #[cfg(test)]
    pub(crate) param_register_aliases: &'a HashMap<String, String>,
    #[cfg(test)]
    pub(crate) carrier_aliases: &'a HashMap<String, String>,
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
    pub(crate) frame_slot_merges: HashMap<String, FrameSlotMergeSummary>,
    pub(crate) frame_object_field_roots: HashMap<FrameObjectFieldKey, SemanticValue>,
    pub(crate) phi_sources: HashMap<String, Vec<SSAVar>>,
    #[cfg(test)]
    pub(crate) formatted_defs: HashMap<String, CExpr>,
    pub(crate) copy_sources_by_value: BTreeMap<ValueId, ValueId>,
    pub(crate) memory_stores: HashMap<String, String>,
    pub(crate) ptr_arith_by_value: BTreeMap<ValueId, PtrArith>,
    pub(crate) ptr_members: HashMap<String, (r2ssa::SSAVar, i64)>,
    pub(crate) condition_values: BTreeSet<ValueId>,
    pub(crate) pinned: HashSet<String>,
    pub(crate) call_result_exprs: BTreeMap<(u64, usize), CExpr>,
    pub(crate) call_result_source_by_value: BTreeMap<ValueId, (u64, usize)>,
    pub(crate) switch_selector_roots: BTreeMap<u64, SemanticValue>,
    #[cfg(test)]
    pub(crate) var_aliases: HashMap<String, String>,
    pub(crate) stack_slots_by_value: BTreeMap<ValueId, StackSlotProvenance>,
    pub(crate) stable_stack_values: HashMap<i64, SemanticValue>,
    pub(crate) stable_memory_values: HashMap<String, SemanticValue>,
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
    pub(crate) unkeyed_writes: std::collections::BTreeMap<&'static str, usize>,
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

    pub(crate) fn display_name(&self) -> String {
        self.var.display_name()
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
pub(crate) struct FlagInfo {
    pub(crate) flag_origins: HashMap<String, (String, String)>,
    pub(crate) compare_provenance: HashMap<String, FlagCompareProvenance>,
    pub(crate) sub_results: HashMap<String, (String, String)>,
    pub(crate) flag_only_values: HashSet<String>,
    pub(crate) predicate_exprs: HashMap<String, CExpr>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FlagCompareKind {
    Equality,
    UnsignedLess,
    SignedNegative,
    Overflow,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FlagCompareProvenance {
    pub(crate) lhs: String,
    pub(crate) rhs: String,
    pub(crate) kind: FlagCompareKind,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Default)]
pub(crate) struct StackInfo {
    pub(crate) stack_vars: HashMap<i64, String>,
    pub(crate) stack_arg_aliases: HashMap<i64, String>,
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

    pub(crate) fn is_scalar(self) -> bool {
        self.value_kind == StackSlotValueKind::Scalar
    }

    pub(crate) fn is_scalar_predicate_carrier(self) -> bool {
        self.predicate_carrier && self.is_scalar()
    }

    pub(crate) fn is_scalar_return_carrier(self) -> bool {
        self.return_carrier && self.is_scalar()
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
        self.frame_object_field_roots
            .retain(|_, value| !semantic_value_references_any(value, &values));
        self.switch_selector_roots
            .retain(|_, value| !semantic_value_references_any(value, &values));
        self.stable_stack_values
            .retain(|_, value| !semantic_value_references_any(value, &values));
        self.stable_memory_values
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
            *self.unkeyed_writes.entry("use_counts").or_default() += 1;
        }
    }

    pub(crate) fn note_condition_var(&mut self, var: &SSAVar) {
        if let Some(value_id) = self.exact_value_id_for_var(var) {
            self.condition_values.insert(value_id);
        } else {
            *self.unkeyed_writes.entry("condition_vars").or_default() += 1;
        }
    }

    #[cfg(test)]
    pub(crate) fn insert_stack_slot_for_name(&mut self, name: &str, slot: StackSlotProvenance) {
        if let Some(value_id) = self.value_id_for_name_or_bind(name) {
            self.stack_slots_by_value.insert(value_id, slot);
        }
    }

    #[cfg(test)]
    pub(crate) fn insert_ptr_arith_for_var(&mut self, var: &SSAVar, ptr: PtrArith) {
        if let Some(value_id) = self.exact_value_id_for_var(var) {
            self.ptr_arith_by_value.insert(value_id, ptr.clone());
        } else {
            *self.unkeyed_writes.entry("ptr_arith").or_default() += 1;
        }
    }

    #[cfg(test)]
    pub(crate) fn insert_forwarded_value_for_var(
        &mut self,
        var: &SSAVar,
        provenance: ValueProvenance,
    ) {
        if let Some(value_id) = self.exact_value_id_for_var(var) {
            self.forwarded_values_by_value
                .insert(value_id, provenance.clone());
        } else {
            *self.unkeyed_writes.entry("forwarded_values").or_default() += 1;
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
            None => *self.unkeyed_writes.entry("semantic_values").or_default() += 1,
        }
    }

    #[cfg(test)]
    pub(crate) fn insert_semantic_value_for_name(&mut self, name: &str, value: SemanticValue) {
        if let Some(value_id) = self.value_id_for_name_or_bind(name) {
            self.semantic_values_by_value.insert(value_id, value);
        } else {
            *self.unkeyed_writes.entry("semantic_values").or_default() += 1;
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

    #[cfg(test)]
    pub(crate) fn insert_call_result_source_alias(
        &mut self,
        alias: &str,
        source_call: (u64, usize),
    ) {
        // The alias names a value; the call it came from is filed against that
        // value. There was a second map from the alias itself, read through
        // `lookup_name_key`, so an alias differing only in case could answer for
        // a call site that belonged to another value.
        match self.value_id_for_name_or_bind(alias) {
            Some(value_id) => {
                self.call_result_source_by_value
                    .insert(value_id, source_call);
            }
            None => {
                *self
                    .unkeyed_writes
                    .entry("call_result_source")
                    .or_default() += 1
            }
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
        self.use_counts_by_value
            .get(&value)
            .copied()
            .unwrap_or(0)
    }

    pub(crate) fn use_count_for_var(&self, var: &SSAVar) -> usize {
        self.exact_value_id_for_var(var)
            .map(|value| self.use_count_for_value(value))
            .unwrap_or(0)
    }

    pub(crate) fn definition_for_value(&self, value_id: ValueId) -> Option<&CExpr> {
        if self.ambiguous_value_ids.contains(&value_id) {
            return None;
        }
        self.definitions_by_value.get(&value_id)
    }

    /// The definition of a value, asked for by the value.
    ///
    /// One precedence. `definition_for_name` and `definition_for_var` both ask
    /// the value-keyed store first and fall back to the name-keyed one; this
    /// asked in the opposite order, so the same question had two answers
    /// depending on which accessor a caller happened to reach for. A value is
    /// the identity here -- a name can be ambiguous and a value cannot -- so the
    /// value-keyed store wins, as it does everywhere else.
    #[cfg(test)]
    pub(crate) fn render_definition_for_value(&self, value_id: ValueId) -> Option<&CExpr> {
        self.definition_for_value(value_id)
    }

    #[cfg(test)]
    pub(crate) fn definition_for_name(&self, name: &str) -> Option<&CExpr> {

        if self.ambiguous_value_names.contains(name) {
            return None;
        }
        self.value_id_for_name(name)
            .and_then(|value_id| self.definitions_by_value.get(&value_id))
    }

    /// Whether this name spells a condition code on this target.
    pub(crate) fn names_a_flag(&self, name: &str) -> bool {
        self.flag_regs
            .contains(&crate::analysis::utils::flag_base_name(name))
    }

    #[cfg(test)]
    pub(crate) fn render_definition_for_name(&self, name: &str) -> Option<&CExpr> {
        self.definition_for_name(name)
    }

    pub(crate) fn semantic_value_for_var(&self, var: &SSAVar) -> Option<&SemanticValue> {
        if self.ambiguous_value_vars.contains(var) {
            return None;
        }
        self.value_id_for_var(var)
            .and_then(|value_id| self.semantic_values_by_value.get(&value_id))
    }

    pub(crate) fn semantic_value_for_value(&self, value_id: ValueId) -> Option<&SemanticValue> {
        if self.ambiguous_value_ids.contains(&value_id) {
            return None;
        }
        self.semantic_values_by_value.get(&value_id)
    }

    #[cfg(test)]
    pub(crate) fn render_semantic_value_for_value(
        &self,
        value_id: ValueId,
    ) -> Option<&SemanticValue> {
        self.semantic_value_for_value(value_id)
    }

    #[cfg(test)]
    pub(crate) fn semantic_value_for_name(&self, name: &str) -> Option<&SemanticValue> {
        if self.ambiguous_value_names.contains(name) {
            return None;
        }
        self.value_id_for_name(name)
            .and_then(|value_id| self.semantic_values_by_value.get(&value_id))
    }

    #[cfg(test)]
    pub(crate) fn render_semantic_value_for_name(&self, name: &str) -> Option<&SemanticValue> {
        self.semantic_value_for_name(name)
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

    pub(crate) fn forwarded_value_for_value(&self, value_id: ValueId) -> Option<&ValueProvenance> {
        if self.ambiguous_value_ids.contains(&value_id) {
            return None;
        }
        self.forwarded_values_by_value.get(&value_id)
    }

    #[cfg(test)]
    pub(crate) fn render_forwarded_value_for_value(
        &self,
        value_id: ValueId,
    ) -> Option<&ValueProvenance> {
        self.forwarded_value_for_value(value_id)
    }

    #[cfg(test)]
    pub(crate) fn forwarded_value_for_name(&self, name: &str) -> Option<&ValueProvenance> {
        if self.ambiguous_value_names.contains(name) {
            return None;
        }
        self.value_id_for_name(name)
            .and_then(|value_id| self.forwarded_values_by_value.get(&value_id))
    }

    #[cfg(test)]
    pub(crate) fn render_forwarded_value_for_name(&self, name: &str) -> Option<&ValueProvenance> {
        self.forwarded_value_for_name(name)
    }

    /// What was copied into this name, as a name.
    ///
    /// The copy is recorded between identities. Spelling the answer back out
    /// means resolving the name to a value, following the copy, and asking what
    /// that value is called -- rather than keeping a second map of names to
    /// names, which `lookup_name_key` matched case-insensitively and so could
    /// answer for a different variable that happened to differ only in case.
    #[cfg(test)]
    pub(crate) fn render_copy_source_for_name(&self, name: &str) -> Option<String> {
        let value_id = self.value_id_for_name(name)?;
        let source_id = self.copy_sources_by_value.get(&value_id)?;
        self.var_for_value_id(*source_id)
            .map(|var| var.display_name())
    }

    /// File a definition against the value a spelling names, if it has none.
    #[cfg(test)]
    pub(crate) fn insert_definition_for_name_if_absent(&mut self, name: &str, expr: CExpr) {
        match self.value_id_for_name_or_bind(name) {
            Some(value_id) => {
                self.definitions_by_value.entry(value_id).or_insert(expr);
            }
            None => *self.unkeyed_writes.entry("definitions").or_default() += 1,
        }
    }

    #[cfg(test)]
    pub(crate) fn stack_slot_for_name(&self, name: &str) -> Option<StackSlotProvenance> {
        if self.ambiguous_value_names.contains(name) {
            return None;
        }
        self.value_id_for_name(name)
            .and_then(|value_id| self.stack_slots_by_value.get(&value_id).copied())
    }

    #[cfg(test)]
    pub(crate) fn render_stack_slot_for_name(&self, name: &str) -> Option<StackSlotProvenance> {
        self.stack_slot_for_name(name)
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

    #[cfg(test)]
    pub(crate) fn is_condition_name(&self, name: &str) -> bool {
        self.value_id_for_name(name)
            .is_some_and(|value| self.is_condition_value(value))
    }

}

impl FlagInfo {
}

impl StackInfo {
}
