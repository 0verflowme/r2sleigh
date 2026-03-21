use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use r2ssa::SSAVar;
use r2types::TypeOracle;

use crate::ast::{CExpr, CType};
use crate::fold::{PtrArith, SSABlock};

// Pass dependency invariant:
// UseInfo -> (FlagInfo, StackInfo) -> PredicateSimplifier -> statement emit.
pub(crate) mod flag_info;
pub(crate) mod lower;
pub(crate) mod ownership;
pub(crate) mod predicate;
pub(crate) mod stack_info;
pub(crate) mod use_info;
pub(crate) mod utils;

pub(crate) use ownership::{
    CallOwner, CallOwnerKind, CallOwnershipFact, CallSiteId, SemanticOwnershipFacts,
};
pub(crate) use predicate::PredicateSimplifier;

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
    pub(crate) use_counts: HashMap<String, usize>,
    pub(crate) definitions: HashMap<String, CExpr>,
    pub(crate) producers: HashMap<String, r2ssa::SSAOp>,
    pub(crate) semantic_values: HashMap<String, SemanticValue>,
    pub(crate) frame_slot_merges: HashMap<String, FrameSlotMergeSummary>,
    pub(crate) frame_object_field_roots: HashMap<FrameObjectFieldKey, SemanticValue>,
    pub(crate) phi_sources: HashMap<String, Vec<SSAVar>>,
    pub(crate) formatted_defs: HashMap<String, CExpr>,
    pub(crate) copy_sources: HashMap<String, String>,
    pub(crate) memory_stores: HashMap<String, String>,
    pub(crate) ptr_arith: HashMap<String, PtrArith>,
    pub(crate) ptr_members: HashMap<String, (r2ssa::SSAVar, i64)>,
    pub(crate) condition_vars: HashSet<String>,
    pub(crate) pinned: HashSet<String>,
    pub(crate) call_args: HashMap<(u64, usize), Vec<CallArgBinding>>,
    pub(crate) call_result_aliases: BTreeMap<(u64, usize), BTreeSet<String>>,
    pub(crate) call_result_exprs: BTreeMap<(u64, usize), CExpr>,
    pub(crate) call_result_source_by_alias: HashMap<String, (u64, usize)>,
    pub(crate) direct_call_result_aliases: HashSet<String>,
    pub(crate) switch_selector_roots: BTreeMap<u64, SemanticValue>,
    pub(crate) consumed_by_call: HashSet<String>,
    pub(crate) inlined_call_results: HashSet<(u64, usize)>,
    pub(crate) var_aliases: HashMap<String, String>,
    pub(crate) type_hints: HashMap<String, CType>,
    pub(crate) stack_slots: HashMap<String, StackSlotProvenance>,
    pub(crate) stable_stack_values: HashMap<i64, SemanticValue>,
    pub(crate) stable_memory_values: HashMap<String, SemanticValue>,
    pub(crate) forwarded_values: HashMap<String, ValueProvenance>,
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
    pub(crate) source_var_name: Option<String>,
}

impl CallArgBinding {
    pub(crate) fn new(arg: SemanticCallArg, role: CallArgRole, stack_offset: Option<i64>) -> Self {
        Self {
            arg,
            role,
            stack_offset,
            source_call: None,
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
    pub(crate) var: SSAVar,
}

impl ValueRef {
    pub(crate) fn new(var: SSAVar) -> Self {
        Self { var }
    }

    pub(crate) fn display_name(&self) -> String {
        self.var.display_name()
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
