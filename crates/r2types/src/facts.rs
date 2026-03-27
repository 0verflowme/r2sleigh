use std::collections::{BTreeMap, HashMap};

use crate::context::{
    ExternalRegisterParamSpec, ExternalStackSlotSpec, ExternalStackVarSpec, StackSlotKey,
    legacy_external_stack_vars_from_slots, stack_slots_from_legacy_external_stack_vars,
};
use crate::convert::CTypeLike;
use crate::external::ExternalTypeDb;
use crate::model::Signedness;

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicReachabilityStatus {
    Reachable,
    Unreachable,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicSemanticMode {
    Raw,
    Compiled,
    Residual,
    VmSummary,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicSemanticSliceClass {
    Wrapper,
    Worker,
    RecursiveGroup,
    InterpreterSwitch,
    InterpreterIndirect,
    GenericLarge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize, Default)]
pub struct SymbolicSemanticCapability {
    pub query_ready: bool,
    pub type_ready: bool,
    pub decompile_ready: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicSemanticResidualReason {
    MissingArch,
    LargeCfg,
    SummaryBudgetExhausted,
    SccBudgetExhausted,
    InterpreterRequiresStepSummary,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicConditionPrecision {
    Exact,
    OverApprox,
    ResidualSearchRequired,
    Unsupported,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicVmUnaryOp {
    Neg,
    Not,
    BoolNot,
    ZExt,
    SExt,
    Trunc,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicVmBinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    SDiv,
    Rem,
    SRem,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    PtrAdd,
    PtrSub,
    Piece,
    Concat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicMemoryRegionKind {
    Stack,
    Global,
    Input,
    Heap,
    Replay,
    EscapedUnknown,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicMemoryRegionRef {
    pub id: u32,
    pub kind: SymbolicMemoryRegionKind,
    pub name: String,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicMemoryRegion {
    Argument { index: usize },
    Region(SymbolicMemoryRegionRef),
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicMemoryCondition {
    pub region: SymbolicMemoryRegion,
    pub offset_lo: i64,
    pub offset_hi: i64,
    pub size: u32,
    pub exact_offset: bool,
    pub expr: String,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicCompiledCondition {
    pub simplified: String,
    pub terms: Vec<String>,
    pub memory_terms: Vec<SymbolicMemoryCondition>,
    pub backward_memory_substitutions: usize,
    pub backward_memory_candidate_enumerations: usize,
    pub backward_memory_residual_fallbacks: usize,
    pub precision: SymbolicConditionPrecision,
    pub supported_paths: usize,
    pub total_paths: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicInterpreterKind {
    SwitchDispatch,
    IndirectDispatch,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicInterpreterDispatch {
    pub kind: SymbolicInterpreterKind,
    pub dispatch_header: u64,
    pub dispatch_targets: usize,
    pub selector: Option<String>,
    pub back_edges: usize,
    pub score: i32,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicVmValueExpr {
    Const(u64),
    Var(String),
    Expr(String),
    Unary {
        op: SymbolicVmUnaryOp,
        expr: Box<SymbolicVmValueExpr>,
    },
    Binary {
        op: SymbolicVmBinaryOp,
        left: Box<SymbolicVmValueExpr>,
        right: Box<SymbolicVmValueExpr>,
    },
}

impl SymbolicVmValueExpr {
    pub fn render(&self) -> String {
        match self {
            Self::Const(value) => format!("0x{value:x}"),
            Self::Var(name) | Self::Expr(name) => name.clone(),
            Self::Unary { op, expr } => {
                let inner = expr.render();
                match op {
                    SymbolicVmUnaryOp::Neg => format!("(-{inner})"),
                    SymbolicVmUnaryOp::Not => format!("(~{inner})"),
                    SymbolicVmUnaryOp::BoolNot => format!("(!{inner})"),
                    SymbolicVmUnaryOp::ZExt => format!("zext({inner})"),
                    SymbolicVmUnaryOp::SExt => format!("sext({inner})"),
                    SymbolicVmUnaryOp::Trunc => format!("trunc({inner})"),
                }
            }
            Self::Binary { op, left, right } => {
                let left = left.render();
                let right = right.render();
                let symbol = match op {
                    SymbolicVmBinaryOp::Add => "+",
                    SymbolicVmBinaryOp::Sub => "-",
                    SymbolicVmBinaryOp::Mul => "*",
                    SymbolicVmBinaryOp::Div | SymbolicVmBinaryOp::SDiv => "/",
                    SymbolicVmBinaryOp::Rem | SymbolicVmBinaryOp::SRem => "%",
                    SymbolicVmBinaryOp::And => "&",
                    SymbolicVmBinaryOp::Or => "|",
                    SymbolicVmBinaryOp::Xor => "^",
                    SymbolicVmBinaryOp::Shl => "<<",
                    SymbolicVmBinaryOp::Shr => ">>",
                    SymbolicVmBinaryOp::Eq => "==",
                    SymbolicVmBinaryOp::Ne => "!=",
                    SymbolicVmBinaryOp::Lt => "<",
                    SymbolicVmBinaryOp::Le => "<=",
                    SymbolicVmBinaryOp::Gt => ">",
                    SymbolicVmBinaryOp::Ge => ">=",
                    SymbolicVmBinaryOp::PtrAdd => "+",
                    SymbolicVmBinaryOp::PtrSub => "-",
                    SymbolicVmBinaryOp::Piece => "piece",
                    SymbolicVmBinaryOp::Concat => "concat",
                };
                match op {
                    SymbolicVmBinaryOp::Piece | SymbolicVmBinaryOp::Concat => {
                        format!("{symbol}({left}, {right})")
                    }
                    SymbolicVmBinaryOp::PtrAdd | SymbolicVmBinaryOp::PtrSub => {
                        format!("({left} {symbol} {right})")
                    }
                    _ => format!("({left} {symbol} {right})"),
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicVmStateUpdate {
    pub output: String,
    pub expr: String,
    pub value: SymbolicVmValueExpr,
    pub exact: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicVmTransferArm {
    pub handler_target: u64,
    pub case_values: Vec<u64>,
    pub region_blocks: Vec<u64>,
    pub exit_targets: Vec<u64>,
    pub state_updates: Vec<SymbolicVmStateUpdate>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub selector_update: Option<SymbolicVmStateUpdate>,
    pub exact: bool,
    pub redispatch: bool,
    pub may_return: bool,
    pub truncated: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicVmStepSummary {
    pub kind: SymbolicInterpreterKind,
    pub loop_header: u64,
    pub dispatch_header: u64,
    pub selector: Option<String>,
    pub dispatch_targets: Vec<u64>,
    pub default_target: Option<u64>,
    pub case_values_by_target: BTreeMap<u64, Vec<u64>>,
    pub loop_latches: Vec<u64>,
    pub state_inputs: Vec<String>,
    pub state_outputs: Vec<String>,
    pub step_blocks: Vec<u64>,
    pub handler_regions: BTreeMap<u64, Vec<u64>>,
    pub handler_state_inputs: BTreeMap<u64, Vec<String>>,
    pub handler_state_outputs: BTreeMap<u64, Vec<String>>,
    pub handler_state_updates: BTreeMap<u64, Vec<SymbolicVmStateUpdate>>,
    pub handler_memory_reads: BTreeMap<u64, usize>,
    pub handler_memory_writes: BTreeMap<u64, usize>,
    pub handler_calls: BTreeMap<u64, usize>,
    pub handler_conditional_branches: BTreeMap<u64, usize>,
    pub handler_exit_targets: BTreeMap<u64, Vec<u64>>,
    pub redispatch_handlers: Vec<u64>,
    pub returning_handlers: Vec<u64>,
    pub truncated_handlers: Vec<u64>,
    pub transfers: Vec<SymbolicVmTransferArm>,
}
pub type SymbolicVmTransferSummary = SymbolicVmStepSummary;

#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicFactDiagnostics {
    pub branches_evaluated: usize,
    pub branches_pruned: usize,
    pub branches_unknown: usize,
    pub skipped_missing_arch: bool,
    pub skipped_large_cfg: bool,
    #[serde(default)]
    pub cache_hit: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic_mode: Option<SymbolicSemanticMode>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic_capability: Option<SymbolicSemanticCapability>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub slice_class: Option<SymbolicSemanticSliceClass>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub residual_reasons: Vec<SymbolicSemanticResidualReason>,
    pub closure_functions: usize,
    pub helper_functions: usize,
    pub derived_summaries: usize,
    pub summary_attempted: usize,
    pub summary_budget_exhausted: usize,
    pub summary_scc_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicBranchFact {
    pub block_addr: u64,
    pub true_target: u64,
    pub false_target: u64,
    pub true_status: SymbolicReachabilityStatus,
    pub false_status: SymbolicReachabilityStatus,
    pub true_condition: Option<String>,
    pub false_condition: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub true_compiled: Option<SymbolicCompiledCondition>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub false_compiled: Option<SymbolicCompiledCondition>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicSemanticFacts {
    pub branch_facts: Vec<SymbolicBranchFact>,
    pub diagnostics: SymbolicFactDiagnostics,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interpreter: Option<SymbolicInterpreterDispatch>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vm_step: Option<SymbolicVmStepSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vm_transfer: Option<SymbolicVmTransferSummary>,
}

impl SymbolicSemanticFacts {
    pub fn is_empty(&self) -> bool {
        self.branch_facts.is_empty()
            && self.diagnostics == SymbolicFactDiagnostics::default()
            && self.interpreter.is_none()
            && self.vm_step.is_none()
            && self.vm_transfer.is_none()
    }

    pub fn branch_fact_for_block(&self, block_addr: u64) -> Option<&SymbolicBranchFact> {
        self.branch_facts
            .iter()
            .find(|fact| fact.block_addr == block_addr)
    }

    pub fn vm_step_for_dispatch_header(
        &self,
        dispatch_header: u64,
    ) -> Option<&SymbolicVmStepSummary> {
        self.vm_step
            .as_ref()
            .filter(|vm_step| vm_step.dispatch_header == dispatch_header)
    }

    pub fn vm_transfer_for_dispatch_header(
        &self,
        dispatch_header: u64,
    ) -> Option<&SymbolicVmTransferSummary> {
        self.vm_transfer
            .as_ref()
            .filter(|vm_transfer| vm_transfer.dispatch_header == dispatch_header)
    }
}

impl SymbolicBranchFact {
    pub fn exact_compiled_condition(&self) -> Option<&SymbolicCompiledCondition> {
        match (self.true_status, self.false_status) {
            (SymbolicReachabilityStatus::Reachable, SymbolicReachabilityStatus::Unreachable) => {
                self.true_compiled.as_ref().filter(|compiled| {
                    matches!(compiled.precision, SymbolicConditionPrecision::Exact)
                })
            }
            (SymbolicReachabilityStatus::Unreachable, SymbolicReachabilityStatus::Reachable) => {
                self.false_compiled.as_ref().filter(|compiled| {
                    matches!(compiled.precision, SymbolicConditionPrecision::Exact)
                })
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub return_type: CTypeLike,
    pub params: Vec<CTypeLike>,
    pub variadic: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalFieldAccessFact {
    pub slot: usize,
    pub field_offset: u64,
    pub field_name: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ResolvedFieldLayout {
    pub owner_name: Option<String>,
    pub field_name: String,
    pub field_offset: u64,
    pub element_stride: Option<u64>,
}

impl ResolvedFieldLayout {
    pub fn direct(
        owner_name: Option<String>,
        field_offset: u64,
        field_name: impl Into<String>,
    ) -> Self {
        Self {
            owner_name,
            field_name: field_name.into(),
            field_offset,
            element_stride: None,
        }
    }

    pub fn indexed(
        owner_name: Option<String>,
        element_stride: u64,
        field_offset: u64,
        field_name: impl Into<String>,
    ) -> Self {
        Self {
            owner_name,
            field_name: field_name.into(),
            field_offset,
            element_stride: Some(element_stride),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionParamSpec {
    pub name: String,
    pub ty: Option<CTypeLike>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionSignatureSpec {
    pub ret_type: Option<CTypeLike>,
    pub params: Vec<FunctionParamSpec>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VisibleBindingKind {
    Param,
    Local,
    StackObject,
    HiddenHome,
    HiddenSaved,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VisibleBinding {
    pub name: String,
    pub ty: Option<CTypeLike>,
    pub kind: VisibleBindingKind,
    pub stack_slot: Option<StackSlotKey>,
    pub param_index: Option<usize>,
    pub source_reg: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CalleeArgEffect {
    pub read: bool,
    pub write: bool,
    pub escape: bool,
    pub free: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalleeMemoryEffectKind {
    Read,
    Write,
    Escape,
    Free,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalleeMemoryRegion {
    Arg { index: usize },
    Global { address: u64 },
    HeapReturn,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeMemoryRange {
    pub offset_lo: i64,
    pub offset_hi: i64,
    pub width: Option<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeMemoryLocation {
    pub region: CalleeMemoryRegion,
    pub range: Option<CalleeMemoryRange>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeMemoryEffect {
    pub kind: CalleeMemoryEffectKind,
    pub location: CalleeMemoryLocation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CalleeReturnRelation {
    Unknown,
    Void,
    Arg(usize),
    Const(u64),
    HeapAlloc,
    Global(u64),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CalleeFact {
    pub function_id: u64,
    pub name: Option<String>,
    pub direct_callees: Vec<u64>,
    pub callsite_count: usize,
    pub has_unknown_calls: bool,
    pub arg_effects: BTreeMap<usize, CalleeArgEffect>,
    pub memory_effects: Vec<CalleeMemoryEffect>,
    pub param_type_hints: BTreeMap<usize, CTypeLike>,
    pub return_type_hint: Option<CTypeLike>,
    pub return_relation: CalleeReturnRelation,
    pub reads_global_memory: bool,
    pub writes_global_memory: bool,
    pub touches_unknown_memory: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InterprocFactDiagnostics {
    pub iterations: usize,
    pub max_iterations: usize,
    pub converged: bool,
    pub scope_size: usize,
    pub scc_count: usize,
    pub max_scc_size: usize,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionTypeFacts {
    pub merged_signature: Option<FunctionSignatureSpec>,
    pub known_function_signatures: HashMap<String, FunctionType>,
    pub register_params: Vec<ExternalRegisterParamSpec>,
    pub stack_slots: BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    pub visible_bindings: Vec<VisibleBinding>,
    pub callee_facts: BTreeMap<u64, CalleeFact>,
    // Legacy compatibility view derived from canonical stack_slots when available.
    pub external_stack_vars: HashMap<i64, ExternalStackVarSpec>,
    pub external_type_db: ExternalTypeDb,
    pub slot_type_overrides: HashMap<usize, String>,
    pub slot_field_profiles: HashMap<usize, BTreeMap<u64, String>>,
    pub symbolic_facts: SymbolicSemanticFacts,
    pub interproc_diagnostics: InterprocFactDiagnostics,
    pub diagnostics: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionTypeFactInputs {
    pub merged_signature: Option<FunctionSignatureSpec>,
    pub known_function_signatures: HashMap<String, FunctionType>,
    pub register_params: Vec<ExternalRegisterParamSpec>,
    pub stack_slots: BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    pub visible_bindings: Vec<VisibleBinding>,
    pub callee_facts: BTreeMap<u64, CalleeFact>,
    pub external_stack_vars: HashMap<i64, ExternalStackVarSpec>,
    pub external_type_db: ExternalTypeDb,
    pub slot_type_overrides: HashMap<usize, String>,
    pub slot_field_profiles: HashMap<usize, BTreeMap<u64, String>>,
    pub symbolic_facts: SymbolicSemanticFacts,
    pub local_field_accesses: Vec<LocalFieldAccessFact>,
    pub interproc_diagnostics: InterprocFactDiagnostics,
    pub diagnostics: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct FunctionTypeFactsBuilder {
    inputs: FunctionTypeFactInputs,
}

impl FunctionTypeFacts {
    pub fn is_empty(&self) -> bool {
        self.merged_signature.is_none()
            && self.known_function_signatures.is_empty()
            && self.register_params.is_empty()
            && self.stack_slots.is_empty()
            && self.visible_bindings.is_empty()
            && self.callee_facts.is_empty()
            && self.external_stack_vars.is_empty()
            && self.external_type_db.structs.is_empty()
            && self.external_type_db.unions.is_empty()
            && self.external_type_db.enums.is_empty()
            && self.external_type_db.diagnostics.is_empty()
            && self.slot_type_overrides.is_empty()
            && self.slot_field_profiles.is_empty()
            && self.symbolic_facts.is_empty()
            && self.interproc_diagnostics == InterprocFactDiagnostics::default()
            && self.diagnostics.is_empty()
    }

    pub fn canonicalized(self) -> Self {
        FunctionTypeFacts::builder(FunctionTypeFactInputs {
            merged_signature: self.merged_signature,
            known_function_signatures: self.known_function_signatures,
            register_params: self.register_params,
            stack_slots: self.stack_slots,
            visible_bindings: self.visible_bindings,
            callee_facts: self.callee_facts,
            external_stack_vars: self.external_stack_vars,
            external_type_db: self.external_type_db,
            slot_type_overrides: self.slot_type_overrides,
            slot_field_profiles: self.slot_field_profiles,
            symbolic_facts: self.symbolic_facts,
            local_field_accesses: Vec::new(),
            interproc_diagnostics: self.interproc_diagnostics,
            diagnostics: self.diagnostics,
        })
        .build()
    }

    pub fn builder(inputs: FunctionTypeFactInputs) -> FunctionTypeFactsBuilder {
        FunctionTypeFactsBuilder::new(inputs)
    }
}

impl FunctionTypeFactsBuilder {
    pub fn new(inputs: FunctionTypeFactInputs) -> Self {
        Self { inputs }
    }

    pub fn build(mut self) -> FunctionTypeFacts {
        merge_local_field_accesses(
            &mut self.inputs.slot_field_profiles,
            &self.inputs.local_field_accesses,
        );

        let FunctionTypeFactInputs {
            merged_signature,
            known_function_signatures,
            register_params,
            mut stack_slots,
            visible_bindings,
            callee_facts,
            external_stack_vars,
            external_type_db,
            slot_type_overrides,
            slot_field_profiles,
            symbolic_facts,
            interproc_diagnostics,
            diagnostics,
            ..
        } = self.inputs;

        if stack_slots.is_empty() && !external_stack_vars.is_empty() {
            stack_slots = stack_slots_from_legacy_external_stack_vars(&external_stack_vars);
        }

        let external_stack_vars = if stack_slots.is_empty() {
            external_stack_vars
        } else {
            legacy_external_stack_vars_from_slots(&stack_slots)
        };

        let mut diagnostics = diagnostics;
        diagnostics.extend(external_type_db.diagnostics.iter().cloned());
        dedup_preserving_order(&mut diagnostics);

        FunctionTypeFacts {
            merged_signature,
            known_function_signatures,
            register_params,
            stack_slots,
            visible_bindings,
            callee_facts,
            external_stack_vars,
            external_type_db,
            slot_type_overrides,
            slot_field_profiles,
            symbolic_facts,
            interproc_diagnostics,
            diagnostics,
        }
    }
}

fn merge_local_field_accesses(
    slot_field_profiles: &mut HashMap<usize, BTreeMap<u64, String>>,
    local_field_accesses: &[LocalFieldAccessFact],
) {
    for access in local_field_accesses {
        slot_field_profiles
            .entry(access.slot)
            .or_default()
            .entry(access.field_offset)
            .or_insert_with(|| access.field_name.clone());
    }
}

fn dedup_preserving_order(items: &mut Vec<String>) {
    let mut seen = std::collections::HashSet::new();
    items.retain(|item| seen.insert(item.clone()));
}

pub fn parse_type_like_spec(spec: &str, ptr_bits: u32) -> Option<CTypeLike> {
    let mut ty = spec.trim();
    if ty.is_empty() {
        return None;
    }

    let mut array_size = None;
    if let Some(start) = ty.rfind('[')
        && ty.ends_with(']')
    {
        let len_str = &ty[start + 1..ty.len() - 1];
        array_size = if len_str.is_empty() {
            Some(None)
        } else {
            len_str.parse::<usize>().ok().map(Some)
        };
        ty = ty[..start].trim_end();
    }

    let mut ptr_count = 0usize;
    while let Some(rest) = ty.strip_suffix('*') {
        ptr_count += 1;
        ty = rest.trim_end();
    }
    let qualifier_filtered = ty
        .split_whitespace()
        .filter(|token| {
            !matches!(
                token.to_ascii_lowercase().as_str(),
                "const"
                    | "volatile"
                    | "restrict"
                    | "__restrict"
                    | "__restrict__"
                    | "__const"
                    | "__const__"
                    | "__volatile"
                    | "__volatile__"
            )
        })
        .collect::<Vec<_>>();
    let qualifier_filtered_storage = (qualifier_filtered.len() != ty.split_whitespace().count())
        .then(|| qualifier_filtered.join(" "));
    if let Some(filtered) = qualifier_filtered_storage.as_deref() {
        ty = filtered.trim();
    }

    let normalize_base = |raw: &str| {
        raw.chars()
            .filter(|ch| !ch.is_whitespace())
            .collect::<String>()
            .to_ascii_lowercase()
    };
    let base_key = normalize_base(ty);

    let mut base = if let Some(rest) = base_key.strip_prefix("int")
        && let Some(bits) = rest.strip_suffix("_t")
    {
        bits.parse::<u32>().ok().map(|bits| CTypeLike::Int {
            bits,
            signedness: Signedness::Signed,
        })
    } else if let Some(rest) = base_key.strip_prefix("uint")
        && let Some(bits) = rest.strip_suffix("_t")
    {
        bits.parse::<u32>().ok().map(|bits| CTypeLike::Int {
            bits,
            signedness: Signedness::Unsigned,
        })
    } else {
        match base_key.as_str() {
            "void" => Some(CTypeLike::Void),
            "bool" => Some(CTypeLike::Bool),
            "char" | "signedchar" => Some(CTypeLike::Int {
                bits: 8,
                signedness: Signedness::Signed,
            }),
            "unsignedchar" => Some(CTypeLike::Int {
                bits: 8,
                signedness: Signedness::Unsigned,
            }),
            "short" | "shortint" | "signedshort" | "signedshortint" => Some(CTypeLike::Int {
                bits: 16,
                signedness: Signedness::Signed,
            }),
            "unsignedshort" | "unsignedshortint" => Some(CTypeLike::Int {
                bits: 16,
                signedness: Signedness::Unsigned,
            }),
            "signed" | "int" | "signedint" => Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            "unsigned" | "unsignedint" => Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Unsigned,
            }),
            "long" | "longint" | "signedlong" | "signedlongint" | "longlong" | "longlongint"
            | "signedlonglong" | "signedlonglongint" => Some(CTypeLike::Int {
                bits: ptr_bits,
                signedness: Signedness::Signed,
            }),
            "unsignedlong"
            | "unsignedlongint"
            | "unsignedlonglong"
            | "unsignedlonglongint"
            | "size_t" => Some(CTypeLike::Int {
                bits: ptr_bits,
                signedness: Signedness::Unsigned,
            }),
            "ssize_t" => Some(CTypeLike::Int {
                bits: ptr_bits,
                signedness: Signedness::Signed,
            }),
            "float" => Some(CTypeLike::Float(32)),
            "double" => Some(CTypeLike::Float(64)),
            _ if ty.to_ascii_lowercase().starts_with("struct ") => ty
                .split_whitespace()
                .nth(1)
                .map(|name| CTypeLike::Struct(name.to_string())),
            _ if ty.to_ascii_lowercase().starts_with("union ") => ty
                .split_whitespace()
                .nth(1)
                .map(|name| CTypeLike::Union(name.to_string())),
            _ if ty.to_ascii_lowercase().starts_with("enum ") => ty
                .split_whitespace()
                .nth(1)
                .map(|name| CTypeLike::Enum(name.to_string())),
            _ => None,
        }
    }?;

    if let Some(size) = array_size {
        base = CTypeLike::Array(Box::new(base), size);
    }
    for _ in 0..ptr_count {
        base = CTypeLike::Pointer(Box::new(base));
    }
    Some(base)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ExternalStackBase, ExternalStackSlotRole};

    #[test]
    fn builder_merges_local_field_accesses_into_slot_profiles() {
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            local_field_accesses: vec![
                LocalFieldAccessFact {
                    slot: 1,
                    field_offset: 0,
                    field_name: "first".to_string(),
                },
                LocalFieldAccessFact {
                    slot: 1,
                    field_offset: 8,
                    field_name: "second".to_string(),
                },
            ],
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts
                .slot_field_profiles
                .get(&1)
                .and_then(|profile| profile.get(&0)),
            Some(&"first".to_string())
        );
        assert_eq!(
            facts
                .slot_field_profiles
                .get(&1)
                .and_then(|profile| profile.get(&8)),
            Some(&"second".to_string())
        );
    }

    #[test]
    fn builder_preserves_explicit_slot_profile_names() {
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            slot_field_profiles: HashMap::from([(
                2,
                BTreeMap::from([(0, "explicit".to_string())]),
            )]),
            local_field_accesses: vec![LocalFieldAccessFact {
                slot: 2,
                field_offset: 0,
                field_name: "local".to_string(),
            }],
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts
                .slot_field_profiles
                .get(&2)
                .and_then(|profile| profile.get(&0)),
            Some(&"explicit".to_string())
        );
    }

    #[test]
    fn builder_merges_external_diagnostics_once() {
        let external = ExternalTypeDb {
            diagnostics: vec!["warning".to_string(), "warning".to_string()],
            ..ExternalTypeDb::default()
        };
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            external_type_db: external,
            diagnostics: vec!["warning".to_string(), "local".to_string()],
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts.diagnostics,
            vec!["warning".to_string(), "local".to_string()]
        );
    }

    #[test]
    fn builder_derives_legacy_stack_var_view_from_canonical_slots() {
        let spec = ExternalStackSlotSpec {
            name: "count".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            stack_slots: BTreeMap::from([(
                StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset: -0x10,
                },
                spec.clone(),
            )]),
            external_stack_vars: HashMap::from([(
                -0x10,
                ExternalStackSlotSpec {
                    name: "stale".to_string(),
                    ..spec.clone()
                },
            )]),
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts
                .external_stack_vars
                .get(&-0x10)
                .map(|slot| slot.name.as_str()),
            Some("count")
        );
    }

    #[test]
    fn builder_canonicalizes_stack_slots_from_legacy_input() {
        let spec = ExternalStackSlotSpec {
            name: "count".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            external_stack_vars: HashMap::from([(-0x10, spec)]),
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts.stack_slots.get(&StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -0x10,
            }),
            facts.external_stack_vars.get(&-0x10)
        );
    }

    #[test]
    fn parse_type_like_spec_accepts_const_qualified_pointers() {
        let signed_char_ptr = CTypeLike::Pointer(Box::new(CTypeLike::Int {
            bits: 8,
            signedness: Signedness::Signed,
        }));
        let void_ptr = CTypeLike::Pointer(Box::new(CTypeLike::Void));

        assert_eq!(
            parse_type_like_spec("char const *", 64),
            Some(signed_char_ptr.clone())
        );
        assert_eq!(
            parse_type_like_spec("const char *", 64),
            Some(signed_char_ptr)
        );
        assert_eq!(parse_type_like_spec("void const *", 64), Some(void_ptr));
    }

    #[test]
    fn symbolic_vm_value_expr_renders_recursive_forms() {
        let expr = SymbolicVmValueExpr::Binary {
            op: SymbolicVmBinaryOp::Add,
            left: Box::new(SymbolicVmValueExpr::Unary {
                op: SymbolicVmUnaryOp::Neg,
                expr: Box::new(SymbolicVmValueExpr::Const(0x10)),
            }),
            right: Box::new(SymbolicVmValueExpr::Binary {
                op: SymbolicVmBinaryOp::Xor,
                left: Box::new(SymbolicVmValueExpr::Var("state".to_string())),
                right: Box::new(SymbolicVmValueExpr::Expr("mask".to_string())),
            }),
        };

        assert_eq!(expr.render(), "((-0x10) + (state ^ mask))");
    }
}
