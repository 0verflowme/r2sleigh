use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use r2ssa::{SSAVar, ValueId};
use r2types::TypeOracle;

use crate::ast::{CExpr, CType};
use crate::fold::{PtrArith, SSABlock};

// Pass dependency invariant:
// UseInfo -> (FlagInfo, StackInfo) -> PredicateSimplifier -> statement emit.
pub(crate) mod flag_info;
pub(crate) mod lower;
pub(crate) mod ownership;
pub(crate) mod predicate;
pub(crate) mod prepared_semantic;
pub(crate) mod stack_info;
pub(crate) mod use_info;
pub(crate) mod utils;

pub(crate) use ownership::{
    CallOwner, CallOwnerKind, CallOwnershipFact, CallSiteId, SemanticOwnershipFacts,
};
pub(crate) use predicate::PredicateSimplifier;
pub(crate) use prepared_semantic::{
    PreparedCallView, PreparedSemanticView, PreparedSemanticViewInputs,
    build_prepared_runtime_facts,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UseInfoAnalysisMode {
    Full,
    LocalStructAccesses,
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

    pub(crate) fn semantic_mut(&mut self) -> &mut UseInfo {
        &mut self.use_info
    }

    pub(crate) fn flags(&self) -> &FlagInfo {
        &self.flag_info
    }

    pub(crate) fn stack(&self) -> &StackInfo {
        &self.stack_info
    }

    pub(crate) fn ownership(&self) -> &SemanticOwnershipFacts {
        &self.ownership
    }
}

#[allow(dead_code)]
#[derive(Clone)]
pub(crate) struct PassEnv<'a> {
    pub(crate) ptr_size: u32,
    pub(crate) sp_name: &'a str,
    pub(crate) fp_name: &'a str,
    pub(crate) ret_reg_name: &'a str,
    pub(crate) function_names: &'a HashMap<u64, String>,
    pub(crate) strings: &'a HashMap<u64, String>,
    pub(crate) symbols: &'a HashMap<u64, String>,
    pub(crate) arg_regs: &'a [String],
    pub(crate) param_register_aliases: &'a HashMap<String, String>,
    pub(crate) caller_saved_regs: &'a HashSet<String>,
    pub(crate) type_hints: &'a HashMap<String, CType>,
    pub(crate) type_oracle: Option<&'a dyn TypeOracle>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Default)]
pub(crate) struct UseInfo {
    pub(crate) value_ids_by_name: HashMap<String, ValueId>,
    pub(crate) vars_by_value_id: BTreeMap<ValueId, SSAVar>,
    pub(crate) use_counts: HashMap<String, usize>,
    pub(crate) use_counts_by_value: BTreeMap<ValueId, usize>,
    pub(crate) definitions: HashMap<String, CExpr>,
    pub(crate) definitions_by_value: BTreeMap<ValueId, CExpr>,
    pub(crate) producers: HashMap<String, r2ssa::SSAOp>,
    pub(crate) semantic_values: HashMap<String, SemanticValue>,
    pub(crate) semantic_values_by_value: BTreeMap<ValueId, SemanticValue>,
    pub(crate) frame_slot_merges: HashMap<String, FrameSlotMergeSummary>,
    pub(crate) frame_object_field_roots: HashMap<FrameObjectFieldKey, SemanticValue>,
    pub(crate) phi_sources: HashMap<String, Vec<SSAVar>>,
    pub(crate) formatted_defs: HashMap<String, CExpr>,
    pub(crate) copy_sources: HashMap<String, String>,
    pub(crate) copy_sources_by_value: BTreeMap<ValueId, ValueId>,
    pub(crate) memory_stores: HashMap<String, String>,
    pub(crate) ptr_arith: HashMap<String, PtrArith>,
    pub(crate) ptr_arith_by_value: BTreeMap<ValueId, PtrArith>,
    pub(crate) ptr_members: HashMap<String, (r2ssa::SSAVar, i64)>,
    pub(crate) condition_vars: HashSet<String>,
    pub(crate) condition_values: BTreeSet<ValueId>,
    pub(crate) pinned: HashSet<String>,
    pub(crate) call_args: HashMap<(u64, usize), Vec<CallArgBinding>>,
    pub(crate) call_result_aliases: BTreeMap<(u64, usize), BTreeSet<String>>,
    pub(crate) call_result_exprs: BTreeMap<(u64, usize), CExpr>,
    pub(crate) call_result_source_by_alias: HashMap<String, (u64, usize)>,
    pub(crate) call_result_source_by_value: BTreeMap<ValueId, (u64, usize)>,
    pub(crate) direct_call_result_aliases: HashSet<String>,
    pub(crate) switch_selector_roots: BTreeMap<u64, SemanticValue>,
    pub(crate) consumed_by_call: HashSet<String>,
    pub(crate) inlined_call_results: HashSet<(u64, usize)>,
    pub(crate) var_aliases: HashMap<String, String>,
    pub(crate) type_hints: HashMap<String, CType>,
    pub(crate) stack_slots: HashMap<String, StackSlotProvenance>,
    pub(crate) stack_slots_by_value: BTreeMap<ValueId, StackSlotProvenance>,
    pub(crate) stable_stack_values: HashMap<i64, SemanticValue>,
    pub(crate) stable_memory_values: HashMap<String, SemanticValue>,
    pub(crate) stable_memory_values_by_value: BTreeMap<ValueId, SemanticValue>,
    pub(crate) forwarded_values: HashMap<String, ValueProvenance>,
    pub(crate) forwarded_values_by_value: BTreeMap<ValueId, ValueProvenance>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum SemanticCallArg {
    Semantic(SemanticValue),
    StringAddr(u64),
    FallbackExpr(CExpr),
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CallArgRole {
    Input,
    Result,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct CallArgBinding {
    pub(crate) arg: SemanticCallArg,
    pub(crate) role: CallArgRole,
    pub(crate) stack_offset: Option<i64>,
    pub(crate) source_call: Option<(u64, usize)>,
    pub(crate) source_value_id: Option<ValueId>,
    pub(crate) source_var_name: Option<String>,
}

impl CallArgBinding {
    pub(crate) fn new(arg: SemanticCallArg, role: CallArgRole, stack_offset: Option<i64>) -> Self {
        Self {
            arg,
            role,
            stack_offset,
            source_call: None,
            source_value_id: None,
            source_var_name: None,
        }
    }

    pub(crate) fn input(arg: SemanticCallArg) -> Self {
        Self::new(arg, CallArgRole::Input, None)
    }

    pub(crate) fn result(arg: SemanticCallArg) -> Self {
        Self::new(arg, CallArgRole::Result, None)
    }

    pub(crate) fn with_stack_offset(mut self, stack_offset: i64) -> Self {
        self.stack_offset = Some(stack_offset);
        self
    }

    pub(crate) fn with_source_call(mut self, block_addr: u64, op_idx: usize) -> Self {
        self.source_call = Some((block_addr, op_idx));
        self
    }

    pub(crate) fn with_source_var(mut self, source_var: &SSAVar) -> Self {
        self.source_var_name = Some(source_var.display_name());
        self
    }

    #[allow(dead_code)]
    pub(crate) fn with_source_value_id(mut self, value_id: ValueId) -> Self {
        self.source_value_id = Some(value_id);
        self
    }

    pub(crate) fn is_result(&self) -> bool {
        self.role == CallArgRole::Result
    }
}

impl From<SemanticCallArg> for CallArgBinding {
    fn from(arg: SemanticCallArg) -> Self {
        Self::input(arg)
    }
}

impl From<CExpr> for CallArgBinding {
    fn from(expr: CExpr) -> Self {
        Self::input(SemanticCallArg::from(expr))
    }
}

impl SemanticCallArg {
    pub(crate) fn semantic(value: SemanticValue) -> Self {
        Self::Semantic(value)
    }

    pub(crate) fn value_root(var: impl Into<ValueRef>) -> Self {
        Self::Semantic(SemanticValue::Scalar(ScalarValue::Root(var.into())))
    }

    pub(crate) fn expr_only(expr: CExpr) -> Self {
        Self::FallbackExpr(expr)
    }
}

impl From<CExpr> for SemanticCallArg {
    fn from(expr: CExpr) -> Self {
        Self::expr_only(expr)
    }
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
    Load { addr: NormalizedAddr, size: u32 },
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

impl UseInfo {
    pub(crate) fn analyze(blocks: &[SSABlock], env: &PassEnv<'_>) -> Self {
        use_info::analyze(blocks, env)
    }

    pub(crate) fn analyze_for_local_struct_accesses(
        blocks: &[SSABlock],
        env: &PassEnv<'_>,
    ) -> Self {
        use_info::analyze_for_local_struct_accesses(blocks, env)
    }

    pub(crate) fn analyze_with_definition_overrides(
        blocks: &[SSABlock],
        env: &PassEnv<'_>,
        definition_overrides: &HashMap<String, CExpr>,
    ) -> Self {
        use_info::analyze_with_definition_overrides(blocks, env, definition_overrides)
    }

    pub(crate) fn preserve_authoritative_facts_from(&mut self, baseline: &UseInfo) {
        use_info::preserve_authoritative_facts(self, baseline);
    }

    pub(crate) fn bind_value_id(&mut self, var: &SSAVar, value_id: ValueId) {
        let display = var.display_name();
        self.value_ids_by_name.insert(display.clone(), value_id);
        self.value_ids_by_name.insert(var.name.clone(), value_id);
        self.vars_by_value_id
            .entry(value_id)
            .or_insert_with(|| var.clone());
    }

    pub(crate) fn note_use_for_var(&mut self, var: &SSAVar) {
        let display = var.display_name();
        *self.use_counts.entry(display).or_insert(0) += 1;
        if let Some(value_id) = self.value_id_for_var(var) {
            *self.use_counts_by_value.entry(value_id).or_insert(0) += 1;
        }
    }

    pub(crate) fn note_condition_var(&mut self, var: &SSAVar) {
        self.condition_vars.insert(var.display_name());
        if let Some(value_id) = self.value_id_for_var(var) {
            self.condition_values.insert(value_id);
        }
    }

    pub(crate) fn insert_definition_for_var(&mut self, var: &SSAVar, expr: CExpr) {
        // Local analysis still derives visible-quality definitions through name-oriented
        // collectors. Keep prepared/runtime id-backed definitions authoritative, but do
        // not blindly promote local definitions into the value-id store yet.
        self.definitions.insert(var.display_name(), expr);
    }

    pub(crate) fn insert_stack_slot_for_var(&mut self, var: &SSAVar, slot: StackSlotProvenance) {
        if let Some(value_id) = self.value_id_for_var(var) {
            self.stack_slots_by_value.insert(value_id, slot);
        }
        self.stack_slots.insert(var.display_name(), slot);
    }

    pub(crate) fn insert_ptr_arith_for_var(&mut self, var: &SSAVar, ptr: PtrArith) {
        if let Some(value_id) = self.value_id_for_var(var) {
            self.ptr_arith_by_value.insert(value_id, ptr.clone());
        }
        self.ptr_arith.insert(var.display_name(), ptr);
    }

    pub(crate) fn insert_forwarded_value_for_var(
        &mut self,
        var: &SSAVar,
        provenance: ValueProvenance,
    ) {
        if let Some(value_id) = self.value_id_for_var(var) {
            self.forwarded_values_by_value
                .insert(value_id, provenance.clone());
        }
        self.forwarded_values.insert(var.display_name(), provenance);
    }

    pub(crate) fn insert_call_result_source_alias(
        &mut self,
        alias: &str,
        source_call: (u64, usize),
    ) {
        self.call_result_source_by_alias
            .insert(alias.to_string(), source_call);
        if let Some(value_id) = self.value_id_for_name(alias) {
            self.call_result_source_by_value
                .insert(value_id, source_call);
        }
    }

    pub(crate) fn value_id_for_var(&self, var: &SSAVar) -> Option<ValueId> {
        self.value_ids_by_name
            .get(&var.display_name())
            .copied()
            .or_else(|| self.value_ids_by_name.get(&var.name).copied())
    }

    pub(crate) fn value_id_for_name(&self, name: &str) -> Option<ValueId> {
        self.value_ids_by_name.get(name).copied()
    }

    pub(crate) fn var_for_value_id(&self, value_id: ValueId) -> Option<&SSAVar> {
        self.vars_by_value_id.get(&value_id)
    }

    pub(crate) fn display_name_for_value_id(&self, value_id: ValueId) -> Option<String> {
        self.var_for_value_id(value_id).map(SSAVar::display_name)
    }

    pub(crate) fn use_count_for_name(&self, name: &str) -> usize {
        self.value_id_for_name(name)
            .and_then(|value_id| self.use_counts_by_value.get(&value_id).copied())
            .or_else(|| self.use_counts.get(name).copied())
            .unwrap_or(0)
    }

    pub(crate) fn definition_for_value(&self, value_id: ValueId) -> Option<&CExpr> {
        self.definitions_by_value.get(&value_id).or_else(|| {
            self.display_name_for_value_id(value_id)
                .as_deref()
                .and_then(|name| self.definitions.get(name))
        })
    }

    pub(crate) fn definition_for_name(&self, name: &str) -> Option<&CExpr> {
        self.definitions.get(name).or_else(|| {
            self.value_id_for_name(name)
                .and_then(|value_id| self.definitions_by_value.get(&value_id))
        })
    }

    pub(crate) fn semantic_value_for_value(&self, value_id: ValueId) -> Option<&SemanticValue> {
        self.semantic_values_by_value.get(&value_id).or_else(|| {
            self.display_name_for_value_id(value_id)
                .as_deref()
                .and_then(|name| self.semantic_values.get(name))
        })
    }

    pub(crate) fn semantic_value_for_name(&self, name: &str) -> Option<&SemanticValue> {
        self.semantic_values.get(name).or_else(|| {
            self.value_id_for_name(name)
                .and_then(|value_id| self.semantic_values_by_value.get(&value_id))
        })
    }

    pub(crate) fn forwarded_value_for_value(&self, value_id: ValueId) -> Option<&ValueProvenance> {
        self.forwarded_values_by_value.get(&value_id).or_else(|| {
            self.display_name_for_value_id(value_id)
                .as_deref()
                .and_then(|name| self.forwarded_values.get(name))
        })
    }

    pub(crate) fn forwarded_value_for_name(&self, name: &str) -> Option<&ValueProvenance> {
        self.forwarded_values.get(name).or_else(|| {
            self.value_id_for_name(name)
                .and_then(|value_id| self.forwarded_values_by_value.get(&value_id))
        })
    }

    pub(crate) fn stack_slot_for_var(&self, var: &SSAVar) -> Option<StackSlotProvenance> {
        self.stack_slots
            .get(&var.display_name())
            .copied()
            .or_else(|| {
                self.value_id_for_var(var)
                    .and_then(|value_id| self.stack_slots_by_value.get(&value_id).copied())
            })
    }

    pub(crate) fn ptr_arith_for_name(&self, name: &str) -> Option<&PtrArith> {
        self.ptr_arith.get(name).or_else(|| {
            self.value_id_for_name(name)
                .and_then(|value_id| self.ptr_arith_by_value.get(&value_id))
        })
    }

    pub(crate) fn is_condition_name(&self, name: &str) -> bool {
        self.value_id_for_name(name)
            .is_some_and(|value_id| self.condition_values.contains(&value_id))
            || self.condition_vars.contains(name)
    }

    pub(crate) fn call_result_source_for_name(&self, name: &str) -> Option<(u64, usize)> {
        self.call_result_source_by_alias
            .get(name)
            .copied()
            .or_else(|| {
                self.value_id_for_name(name)
                    .and_then(|value_id| self.call_result_source_by_value.get(&value_id).copied())
            })
    }
}

impl FlagInfo {
    pub(crate) fn analyze(blocks: &[SSABlock], use_info: &UseInfo, env: &PassEnv<'_>) -> Self {
        flag_info::analyze(blocks, use_info, env)
    }
}

impl StackInfo {
    pub(crate) fn analyze(blocks: &[SSABlock], use_info: &UseInfo, env: &PassEnv<'_>) -> Self {
        stack_info::analyze(blocks, use_info, env)
    }
}
