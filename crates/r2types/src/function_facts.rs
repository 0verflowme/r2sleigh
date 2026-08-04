use std::collections::{BTreeMap, HashMap};

use serde::{Deserialize, Serialize};

use crate::callee::{CalleeIdentityContext, CalleeResolutionFacts, CallsiteKey};
use crate::context::{ExternalStackBase, ExternalStackSlotRole, StackSlotKey};
use crate::facts::{
    FunctionSignatureProjection, FunctionSignatureSpec, FunctionTypeFacts,
    OutParamCertificateEvidence, OutParamCertificateSource, SignatureProjectionResult,
    VisibleBindingKind,
};
use crate::{CTypeLike, normalize_external_type_name, parse_type_like_spec};

pub type OpSiteKey = (u64, usize);
pub type MemoryOpSiteKey = (u64, usize, bool);

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ParamSlotResolver {
    slots_by_register: BTreeMap<String, usize>,
}

impl ParamSlotResolver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_arch_name(arch_name: Option<&str>) -> Self {
        let (arg_regs, _, _) = crate::prepare::recover_vars_arch_profile(arch_name);
        Self::from_arg_alias_map(arg_regs)
    }

    pub fn from_arg_alias_map(arg_regs: crate::prepare::ArgAliasMap) -> Self {
        let mut resolver = Self::new();
        for (slot, (canonical, aliases)) in arg_regs.iter().enumerate() {
            resolver.insert_alias(canonical, slot);
            for alias in *aliases {
                resolver.insert_alias(alias, slot);
            }
        }
        resolver
    }

    pub fn from_arg_regs<I, S>(arg_regs: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let mut resolver = Self::new();
        for (slot, reg) in arg_regs.into_iter().enumerate() {
            resolver.insert_register_family_aliases(reg.as_ref(), slot);
        }
        resolver
    }

    pub fn is_empty(&self) -> bool {
        self.slots_by_register.is_empty()
    }

    pub fn insert_alias(&mut self, register: &str, slot: usize) {
        let normalized = normalize_param_slot_register_name(register);
        if normalized.is_empty() {
            return;
        }
        self.slots_by_register.entry(normalized).or_insert(slot);
    }

    pub fn slot_for_register_name(&self, register: &str) -> Option<usize> {
        let normalized = normalize_param_slot_register_name(register);
        self.slots_by_register.get(&normalized).copied()
    }

    pub fn slot_for_var(&self, var: &r2ssa::SSAVar) -> Option<usize> {
        if var.version != 0 || !var.is_register() || var.is_memory() {
            return None;
        }
        self.slot_for_register_name(&var.name)
    }

    fn insert_register_family_aliases(&mut self, register: &str, slot: usize) {
        let normalized = normalize_param_slot_register_name(register);
        if normalized.is_empty() {
            return;
        }
        self.insert_alias(&normalized, slot);
        for alias in inferred_param_slot_register_aliases(&normalized) {
            self.insert_alias(&alias, slot);
        }
    }
}

fn normalize_param_slot_register_name(register: &str) -> String {
    register.trim_start_matches('$').to_ascii_lowercase()
}

fn inferred_param_slot_register_aliases(register: &str) -> Vec<String> {
    match register {
        "rax" => {
            return ["eax", "ax", "al", "ah"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "eax" | "ax" | "al" | "ah" => return vec!["rax".to_string()],
        "rbx" => {
            return ["ebx", "bx", "bl", "bh"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "ebx" | "bx" | "bl" | "bh" => return vec!["rbx".to_string()],
        "rcx" => {
            return ["ecx", "cx", "cl", "ch"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "ecx" | "cx" | "cl" | "ch" => return vec!["rcx".to_string()],
        "rdx" => {
            return ["edx", "dx", "dl", "dh"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "edx" | "dx" | "dl" | "dh" => return vec!["rdx".to_string()],
        "rsi" => {
            return ["esi", "si", "sil"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "esi" | "si" | "sil" => return vec!["rsi".to_string()],
        "rdi" => {
            return ["edi", "di", "dil"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "edi" | "di" | "dil" => return vec!["rdi".to_string()],
        "rbp" => {
            return ["ebp", "bp", "bpl"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "ebp" | "bp" | "bpl" => return vec!["rbp".to_string()],
        "rsp" => {
            return ["esp", "sp", "spl"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "esp" | "sp" | "spl" => return vec!["rsp".to_string()],
        _ => {}
    }

    if let Some(rest) = register.strip_prefix('r')
        && let Some(index) = rest.strip_suffix('d').or_else(|| rest.strip_suffix('w'))
        && index.chars().all(|c| c.is_ascii_digit())
    {
        return vec![format!("r{index}")];
    }
    if let Some(index) = register.strip_prefix('r')
        && index.chars().all(|c| c.is_ascii_digit())
    {
        return vec![
            format!("r{index}d"),
            format!("r{index}w"),
            format!("r{index}b"),
        ];
    }
    if let Some(index) = register.strip_prefix('x')
        && index.chars().all(|c| c.is_ascii_digit())
    {
        return vec![format!("w{index}")];
    }
    if let Some(index) = register.strip_prefix('w')
        && index.chars().all(|c| c.is_ascii_digit())
    {
        return vec![format!("x{index}")];
    }
    if let Some(index) = register.strip_prefix('a')
        && let Ok(index) = index.parse::<u8>()
        && index <= 7
    {
        return vec![format!("x{}", index + 10)];
    }
    if let Some(index) = register.strip_prefix('x')
        && let Ok(index) = index.parse::<u8>()
        && (10..=17).contains(&index)
    {
        return vec![format!("a{}", index - 10)];
    }

    Vec::new()
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnalysisPlans {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifact_build: Option<r2sym::ArtifactBuildPlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub query: Option<r2sym::QueryPlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_plan: Option<r2sym::TypePlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub decompile: Option<r2sym::DecompilePlan>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionCallsiteFacts {
    pub by_callsite: BTreeMap<CallsiteKey, CallsiteArgumentFacts>,
}

impl FunctionCallsiteFacts {
    pub fn is_empty(&self) -> bool {
        self.by_callsite.is_empty()
    }

    pub fn arguments_for_site(&self, callsite: CallsiteKey) -> Option<&CallsiteArgumentFacts> {
        self.by_callsite.get(&callsite)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionCallResultFacts {
    pub by_value: BTreeMap<r2ssa::ValueId, CallResultFact>,
    pub by_callsite: BTreeMap<CallsiteKey, Vec<r2ssa::ValueId>>,
}

impl FunctionCallResultFacts {
    pub fn is_empty(&self) -> bool {
        self.by_value.is_empty() && self.by_callsite.is_empty()
    }

    pub fn result_for_value(&self, value: r2ssa::ValueId) -> Option<&CallResultFact> {
        self.by_value.get(&value)
    }

    pub fn results_for_site(&self, callsite: CallsiteKey) -> impl Iterator<Item = &CallResultFact> {
        self.by_callsite
            .get(&callsite)
            .into_iter()
            .flatten()
            .filter_map(|value| self.by_value.get(value))
    }

    pub fn owner_for_site(&self, callsite: CallsiteKey) -> Option<&r2ssa::ValueOwner> {
        self.results_for_site(callsite)
            .find_map(|result| result.owner.as_ref())
    }

    pub fn owner_for_value(&self, value: r2ssa::ValueId) -> Option<&r2ssa::ValueOwner> {
        self.result_for_value(value)
            .and_then(|result| result.owner.as_ref())
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionCallRenderFacts {
    pub by_callsite: BTreeMap<CallsiteKey, CallsiteRenderFact>,
}

impl FunctionCallRenderFacts {
    pub fn is_empty(&self) -> bool {
        self.by_callsite.is_empty()
    }

    pub fn fact_for_site(&self, callsite: CallsiteKey) -> Option<&CallsiteRenderFact> {
        self.by_callsite.get(&callsite)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallsiteRenderFact {
    pub callsite: CallsiteKey,
    pub target: Option<r2ssa::ValueId>,
    pub disposition: CallsiteRenderDisposition,
    pub proof_values: Vec<r2ssa::ValueId>,
    pub residual_reason: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CallsiteRenderDisposition {
    SideEffectStatement,
    AssignedResult,
    NestedExpression,
    Suppressed,
    Residualized,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionControlFacts {
    pub branch_predicates: BTreeMap<u64, BranchPredicateFact>,
    pub block_assumptions: BTreeMap<u64, Vec<ControlBlockAssumptionFact>>,
    pub loops: BTreeMap<r2ssa::LoopId, LoopStructureFact>,
    pub switches: BTreeMap<u64, SwitchSelectorFact>,
}

impl FunctionControlFacts {
    pub fn is_empty(&self) -> bool {
        self.branch_predicates.is_empty()
            && self.block_assumptions.is_empty()
            && self.loops.is_empty()
            && self.switches.is_empty()
    }

    pub fn branch_for_block(&self, block_addr: u64) -> Option<&BranchPredicateFact> {
        self.branch_predicates.get(&block_addr)
    }

    pub fn switch_for_block(&self, block_addr: u64) -> Option<&SwitchSelectorFact> {
        self.switches.get(&block_addr)
    }

    pub fn loops_for_header(&self, header: u64) -> impl Iterator<Item = &LoopStructureFact> + '_ {
        self.loops
            .values()
            .filter(move |fact| fact.header == header)
    }

    pub fn assumptions_for_block(
        &self,
        block_addr: u64,
    ) -> impl Iterator<Item = &ControlBlockAssumptionFact> {
        self.block_assumptions
            .get(&block_addr)
            .into_iter()
            .flatten()
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionRenderFacts {
    pub expressions: BTreeMap<r2ssa::ValueId, ExpressionRenderFact>,
    pub string_literals_by_value: BTreeMap<r2ssa::ValueId, StringLiteralRenderFact>,
    pub memory_accesses: BTreeMap<r2ssa::StructuredAccessId, MemoryAccessRenderFact>,
    pub memory_accesses_by_op: BTreeMap<MemoryOpSiteKey, Vec<r2ssa::StructuredAccessId>>,
    pub member_accesses_by_op: BTreeMap<MemoryOpSiteKey, Vec<MemberAccessRenderFact>>,
    pub array_accesses_by_op: BTreeMap<MemoryOpSiteKey, Vec<ArrayAccessRenderFact>>,
    pub returns_by_op: BTreeMap<OpSiteKey, ReturnValueRenderFact>,
    pub stack_slot_offsets: BTreeMap<r2ssa::ObjectId, i64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackSlotOwnerRenderAuthorization {
    pub object: r2ssa::ObjectId,
    pub offset: i64,
    pub name: String,
}

impl FunctionRenderFacts {
    pub fn is_empty(&self) -> bool {
        self.expressions.is_empty()
            && self.string_literals_by_value.is_empty()
            && self.memory_accesses.is_empty()
            && self.memory_accesses_by_op.is_empty()
            && self.member_accesses_by_op.is_empty()
            && self.array_accesses_by_op.is_empty()
            && self.returns_by_op.is_empty()
            && self.stack_slot_offsets.is_empty()
    }

    pub fn expression_for_value(&self, value: r2ssa::ValueId) -> Option<&ExpressionRenderFact> {
        self.expressions.get(&value)
    }

    pub fn expression_is_renderable(&self, value: r2ssa::ValueId) -> bool {
        self.expression_for_value(value)
            .is_some_and(|fact| fact.renderable)
    }

    pub fn string_literal_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<&StringLiteralRenderFact> {
        self.string_literals_by_value.get(&value)
    }

    pub fn memory_access_for_op(
        &self,
        block_addr: u64,
        op_index: usize,
        is_write: bool,
    ) -> Option<&MemoryAccessRenderFact> {
        self.memory_accesses_by_op
            .get(&(block_addr, op_index, is_write))?
            .iter()
            .filter_map(|access| self.memory_accesses.get(access))
            .find(|fact| fact.width > 0)
    }

    pub fn return_for_op(
        &self,
        block_addr: u64,
        op_index: usize,
    ) -> Option<&ReturnValueRenderFact> {
        self.returns_by_op.get(&(block_addr, op_index))
    }

    pub fn member_access_for_op(
        &self,
        block_addr: u64,
        op_index: usize,
        is_write: bool,
        field_name: &str,
        field_offset: u64,
        access_width: Option<u32>,
    ) -> Option<&MemberAccessRenderFact> {
        self.member_accesses_by_op
            .get(&(block_addr, op_index, is_write))?
            .iter()
            .find(|fact| {
                let Some(memory) = self.memory_accesses.get(&fact.access) else {
                    return false;
                };
                memory.block_addr == block_addr
                    && memory.op_index == op_index
                    && memory.is_write == is_write
                    && memory.object == fact.object
                    && memory.width == fact.access_width
                    && fact.field_offset == field_offset
                    && fact.field_name.eq_ignore_ascii_case(field_name)
                    && access_width.is_none_or(|width| fact.access_width == width)
            })
    }

    pub fn member_access_for_op_any_direction(
        &self,
        block_addr: u64,
        op_index: usize,
        field_name: &str,
        field_offset: u64,
        access_width: Option<u32>,
    ) -> Option<&MemberAccessRenderFact> {
        self.member_access_for_op(
            block_addr,
            op_index,
            false,
            field_name,
            field_offset,
            access_width,
        )
        .or_else(|| {
            self.member_access_for_op(
                block_addr,
                op_index,
                true,
                field_name,
                field_offset,
                access_width,
            )
        })
    }

    pub fn array_access_for_op(
        &self,
        block_addr: u64,
        op_index: usize,
        is_write: bool,
        field_offset: u64,
        element_stride: u64,
        access_width: Option<u32>,
    ) -> Option<&ArrayAccessRenderFact> {
        self.array_accesses_by_op
            .get(&(block_addr, op_index, is_write))?
            .iter()
            .find(|fact| {
                let Some(memory) = self.memory_accesses.get(&fact.access) else {
                    return false;
                };
                memory.block_addr == block_addr
                    && memory.op_index == op_index
                    && memory.is_write == is_write
                    && memory.object == fact.object
                    && memory.width == fact.access_width
                    && fact.field_offset == field_offset
                    && fact.element_stride == element_stride
                    && access_width.is_none_or(|width| fact.access_width == width)
            })
    }

    pub fn array_access_for_op_any_direction(
        &self,
        block_addr: u64,
        op_index: usize,
        field_offset: u64,
        element_stride: u64,
        access_width: Option<u32>,
    ) -> Option<&ArrayAccessRenderFact> {
        self.array_access_for_op(
            block_addr,
            op_index,
            false,
            field_offset,
            element_stride,
            access_width,
        )
        .or_else(|| {
            self.array_access_for_op(
                block_addr,
                op_index,
                true,
                field_offset,
                element_stride,
                access_width,
            )
        })
    }

    pub fn has_stack_slot_offset(&self, offset: i64) -> bool {
        self.stack_slot_offsets
            .values()
            .any(|slot_offset| *slot_offset == offset)
    }
}

fn stack_slot_offset(slot: &StackSlotKey) -> i64 {
    match slot.base {
        ExternalStackBase::FramePointer => -slot.offset,
        _ => slot.offset,
    }
}

fn stack_slot_matches_offset(slot: &StackSlotKey, offset: i64) -> bool {
    stack_slot_offset(slot) == offset
}

fn visible_stack_binding_kind_is_renderable(kind: &VisibleBindingKind) -> bool {
    matches!(
        kind,
        VisibleBindingKind::Param | VisibleBindingKind::Local | VisibleBindingKind::StackObject
    )
}

fn external_stack_slot_role_is_renderable(role: ExternalStackSlotRole) -> bool {
    matches!(
        role,
        ExternalStackSlotRole::Local | ExternalStackSlotRole::StackArg
    )
}

fn recovered_stack_owner_name_is_renderable(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    !lower.is_empty()
        && lower != "stack"
        && lower != "slot"
        && lower != "saved_fp"
        && lower != "fake_stack_slot"
        && !lower.starts_with("stack_")
        && !lower.starts_with("slot_")
        && !lower.starts_with("local_")
        && !lower.starts_with("arg_")
        && !lower.starts_with("var_")
}

fn remember_stack_param_owner_name(candidate: &mut Option<String>, name: &str) -> Option<()> {
    let name = name.trim();
    if name.is_empty() {
        return Some(());
    }
    if let Some(existing) = candidate.as_ref() {
        return existing.eq_ignore_ascii_case(name).then_some(());
    }
    *candidate = Some(name.to_string());
    Some(())
}

fn stack_owner_type_is_renderable(ty: &CTypeLike) -> bool {
    !matches!(ty, CTypeLike::Unknown | CTypeLike::Void)
}

fn signature_param_name_type_is_renderable(
    signature: Option<&FunctionSignatureSpec>,
    name: &str,
) -> bool {
    signature
        .into_iter()
        .flat_map(|signature| signature.params.iter())
        .any(|param| {
            param.name.eq_ignore_ascii_case(name)
                && param
                    .ty
                    .as_ref()
                    .is_some_and(stack_owner_type_is_renderable)
        })
}

fn type_like_size_bytes(ty: &CTypeLike, ptr_bits: u32) -> Option<u64> {
    match ty {
        CTypeLike::Void | CTypeLike::Unknown | CTypeLike::Function => None,
        CTypeLike::Bool => Some(1),
        CTypeLike::Int { bits, .. } | CTypeLike::Float(bits) => {
            Some((u64::from(*bits).saturating_add(7) / 8).max(1))
        }
        CTypeLike::Pointer(_) => Some((ptr_bits / 8).max(1) as u64),
        CTypeLike::Array(inner, Some(count)) => {
            type_like_size_bytes(inner, ptr_bits).map(|size| size.saturating_mul(*count as u64))
        }
        CTypeLike::Array(inner, None) => type_like_size_bytes(inner, ptr_bits),
        CTypeLike::Struct(_) | CTypeLike::Union(_) | CTypeLike::Enum(_) | CTypeLike::Typedef(_) => {
            None
        }
    }
}

fn field_certificate_width_matches(
    cert: &crate::facts::FieldAccessCertificate,
    access_width: u32,
    ptr_bits: u32,
) -> bool {
    cert.field_type
        .as_deref()
        .and_then(|field_type| parse_type_like_spec(field_type, ptr_bits))
        .and_then(|ty| type_like_size_bytes(&ty, ptr_bits))
        .is_none_or(|width| width == u64::from(access_width))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpressionRenderFact {
    pub value: r2ssa::ValueId,
    pub defining_inst: Option<r2ssa::InstId>,
    pub width: u32,
    pub renderable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryAccessRenderFact {
    pub access: r2ssa::StructuredAccessId,
    pub block_addr: u64,
    pub op_index: usize,
    pub object: r2ssa::ObjectId,
    pub address: r2ssa::ValueId,
    pub value: Option<r2ssa::ValueId>,
    pub is_write: bool,
    pub width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringLiteralRenderFact {
    pub value: r2ssa::ValueId,
    pub address: u64,
    pub text: String,
    pub source: StringLiteralRenderSource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringLiteralRenderSource {
    TypedFunctionFacts,
    Radare2TypedCollector,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemberAccessRenderFact {
    pub access: r2ssa::StructuredAccessId,
    pub block_addr: u64,
    pub op_index: usize,
    pub object: r2ssa::ObjectId,
    pub is_write: bool,
    pub field_offset: u64,
    pub field_name: String,
    pub access_width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrayAccessRenderFact {
    pub access: r2ssa::StructuredAccessId,
    pub block_addr: u64,
    pub op_index: usize,
    pub object: r2ssa::ObjectId,
    pub is_write: bool,
    pub field_offset: u64,
    pub element_stride: u64,
    pub access_width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnValueRenderFact {
    pub block_addr: u64,
    pub op_index: usize,
    pub value: r2ssa::ValueId,
    pub width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchPredicateFact {
    pub id: r2ssa::PredicateId,
    pub block_addr: u64,
    pub condition: r2ssa::ValueId,
    pub comparison: Option<PredicateComparisonFact>,
    pub true_target: u64,
    pub false_target: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PredicateComparisonFact {
    pub kind: r2ssa::CompareKind,
    pub lhs: r2ssa::ValueId,
    pub rhs: r2ssa::ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ControlBlockAssumptionFact {
    pub predecessor: u64,
    pub predicate: r2ssa::PredicateId,
    pub truth: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopStructureFact {
    pub loop_id: r2ssa::LoopId,
    pub proof_node: String,
    pub header: u64,
    pub condition: Option<r2ssa::PredicateId>,
    pub condition_value: Option<r2ssa::ValueId>,
    pub body: Vec<u64>,
    pub latches: Vec<u64>,
    pub exits: Vec<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchSelectorFact {
    pub proof_node: String,
    pub block_addr: u64,
    pub selector: Option<r2ssa::ValueId>,
    pub cases: Vec<(u64, u64)>,
    pub default: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallResultFact {
    pub callsite: CallsiteKey,
    pub call_site_id: r2ssa::CallSiteId,
    pub at: r2ssa::InstId,
    pub value: r2ssa::ValueId,
    pub width: u32,
    pub carrier: r2ssa::ReturnCarrier,
    pub owner: Option<r2ssa::ValueOwner>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallsiteArgumentFacts {
    pub callsite: CallsiteKey,
    pub call_site_id: r2ssa::CallSiteId,
    pub at: r2ssa::InstId,
    pub target: r2ssa::ValueId,
    pub direct_target: Option<u64>,
    pub argument_values: Vec<CallArgumentValueFact>,
    pub register_argument_locations: Vec<RegisterCallArgumentLocationFact>,
    pub stack_argument_locations: Vec<StackCallArgumentLocationFact>,
}

impl CallsiteArgumentFacts {
    pub fn argument_value(&self, index: usize) -> Option<r2ssa::ValueId> {
        self.argument_values
            .iter()
            .find(|argument| argument.index == index)
            .map(|argument| argument.value)
    }

    pub fn canonical_argument_values(&self) -> Vec<r2ssa::ValueId> {
        let mut by_index = BTreeMap::new();
        for argument in &self.argument_values {
            by_index.insert(argument.index, argument.value);
        }
        for argument in &self.stack_argument_locations {
            by_index.entry(argument.index).or_insert(argument.value);
        }
        by_index.into_values().collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallArgumentValueFact {
    pub index: usize,
    pub value: r2ssa::ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegisterCallArgumentLocationFact {
    pub index: usize,
    pub value: r2ssa::ValueId,
    pub name: String,
    pub source_inst: Option<r2ssa::InstId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StackCallArgumentLocationFact {
    pub index: usize,
    pub value: r2ssa::ValueId,
    pub object: r2ssa::ObjectId,
    pub offset: i64,
    pub memory_access: r2ssa::StructuredAccessId,
    pub source_inst: Option<r2ssa::InstId>,
}

impl AnalysisPlans {
    pub fn from_semantics(semantics: Option<&r2sym::SemanticArtifact>) -> Self {
        let Some(semantics) = semantics else {
            return Self::default();
        };
        Self {
            artifact_build: Some(semantics.build_plan()),
            query: Some(semantics.query_plan()),
            type_plan: Some(semantics.type_plan()),
            decompile: Some(semantics.decompile_plan()),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterprocSummaryView {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub set: Option<r2ssa::InterprocSummarySet>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rollup: Option<SummaryEffectRollup>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub helpers: Vec<SummaryHelperView>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SummaryEffectRollup {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub root_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub root_return_relation: Option<r2ssa::SummaryReturnRelation>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub out_param_facts: Vec<SummaryOutParamFact>,
    #[serde(default)]
    pub pointer_param_indices: Vec<usize>,
    #[serde(default)]
    pub transfer_count: usize,
    #[serde(default)]
    pub allocation_count: usize,
    #[serde(default)]
    pub lifetime_count: usize,
    #[serde(default)]
    pub sync_count: usize,
    #[serde(default)]
    pub atomic_count: usize,
    pub helper_summary_count: usize,
    pub has_unknown_calls: bool,
    pub touches_unknown_memory: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SummaryHelperView {
    pub function_id: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub arg_count_hint: Option<usize>,
    pub return_relation: r2ssa::SummaryReturnRelation,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub out_param_facts: Vec<SummaryOutParamFact>,
    #[serde(default)]
    pub pointer_param_indices: Vec<usize>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub transfer_effects: Vec<r2ssa::SummaryTransferEffect>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub allocation_effects: Vec<r2ssa::SummaryAllocationEffect>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub lifetime_effects: Vec<r2ssa::SummaryLifetimeEffect>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub sync_effects: Vec<r2ssa::SummarySyncEffect>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub atomic_effects: Vec<r2ssa::SummaryAtomicEffect>,
    pub has_unknown_calls: bool,
    pub touches_unknown_memory: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SummaryOutParamFact {
    pub param_index: usize,
    pub evidence: OutParamCertificateEvidence,
    pub source: OutParamCertificateSource,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecompileCapabilityView {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub plan: Option<r2sym::DecompilePlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub slice_class: Option<r2sym::SliceClass>,
    pub skipped_large_cfg: bool,
    pub has_native_regions: bool,
    pub has_summary_islands: bool,
    pub has_primary_summary_islands: bool,
    pub summary_island_count: usize,
    pub primary_summary_island_count: usize,
    pub generic_memory_summary_count: usize,
    pub has_memory_read_write_summary_pair: bool,
    pub actionable_region_count: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub ambiguous_targets: Vec<u64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub residual_reasons: Vec<r2sym::ResidualReason>,
    pub assumption_conflicted: bool,
    pub summary_conflicted: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DecompileRouteKind {
    Standard,
    StructuredWorker,
    SummaryIslands,
    LinearWorker,
    VmSummary,
    FallbackComment,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecompileRouteFacts {
    pub kind: DecompileRouteKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fallback_comment: Option<String>,
    pub skip_runtime_type_inference: bool,
    pub use_prepared_semantic_view: bool,
    pub proof_coverage: r2sym::ProofCoverage,
    pub render_permission: r2sym::RenderPermission,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionInputQualityFacts {
    pub expected_blocks: usize,
    pub lifted_blocks: usize,
    pub actual_lifted_blocks: usize,
    pub read_failures: usize,
    pub invalid_blocks: usize,
    pub null_lift_failures: usize,
    pub truncated_blocks: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub refusal_reason: Option<String>,
}

impl FunctionInputQualityFacts {
    pub fn is_complete(&self) -> bool {
        self.refusal_reason.is_none()
            && self.expected_blocks > 0
            && self.lifted_blocks > 0
            && self.expected_blocks == self.lifted_blocks
            && self.lifted_blocks == self.actual_lifted_blocks
            && self.read_failures == 0
            && self.invalid_blocks == 0
            && self.null_lift_failures == 0
            && self.truncated_blocks == 0
    }
}

impl InterprocSummaryView {
    pub fn new(set: Option<r2ssa::InterprocSummarySet>) -> Self {
        let rollup = summary_rollup(set.as_ref());
        let helpers = helper_views(set.as_ref());
        Self {
            set,
            rollup,
            helpers,
        }
    }

    pub fn as_set(&self) -> Option<&r2ssa::InterprocSummarySet> {
        self.set.as_ref()
    }

    pub fn root_summary(&self) -> Option<&r2ssa::FunctionSemanticSummary> {
        let set = self.set.as_ref()?;
        let root = set.root?;
        set.summaries.get(&root)
    }

    pub fn diagnostics(&self) -> Option<&r2ssa::InterprocSummaryDiagnostics> {
        self.set.as_ref().map(|set| &set.diagnostics)
    }

    pub fn helper_summary_for_name(&self, name: &str) -> Option<&r2ssa::FunctionSemanticSummary> {
        let normalized = name.trim().to_ascii_lowercase();
        self.set.as_ref()?.summaries.values().find(|summary| {
            summary
                .name
                .as_deref()
                .is_some_and(|summary_name| summary_name.trim().to_ascii_lowercase() == normalized)
        })
    }

    pub fn helper_view_for_name(&self, name: &str) -> Option<&SummaryHelperView> {
        let normalized = name.trim().to_ascii_lowercase();
        self.helpers.iter().find(|summary| {
            summary
                .name
                .as_deref()
                .is_some_and(|summary_name| summary_name.trim().to_ascii_lowercase() == normalized)
        })
    }

    pub fn out_param_indices(&self) -> Vec<usize> {
        out_param_indices_from_facts(
            self.rollup
                .as_ref()
                .map(|rollup| rollup.out_param_facts.as_slice())
                .unwrap_or(&[]),
        )
    }

    pub fn pointer_param_indices(&self) -> &[usize] {
        self.rollup
            .as_ref()
            .map(|rollup| rollup.pointer_param_indices.as_slice())
            .unwrap_or(&[])
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionFacts {
    types: FunctionTypeFacts,
    semantics: Option<r2sym::SemanticArtifact>,
    proof: r2sym::ProofCoverage,
    decompile_route: Option<DecompileRouteFacts>,
    input_quality: Option<FunctionInputQualityFacts>,
    callee_resolution: CalleeResolutionFacts,
    callsites: FunctionCallsiteFacts,
    call_results: FunctionCallResultFacts,
    call_render: FunctionCallRenderFacts,
    control: FunctionControlFacts,
    render: FunctionRenderFacts,
    assumptions: r2ssa::AssumptionSet,
    plans: AnalysisPlans,
    summary_view: InterprocSummaryView,
    diagnostics: Vec<String>,
    assumption_usage: r2ssa::AssumptionUsageReport,
}

impl FunctionFacts {
    pub fn new(types: FunctionTypeFacts, semantics: Option<r2sym::SemanticArtifact>) -> Self {
        let plans = AnalysisPlans::from_semantics(semantics.as_ref());
        let proof = semantics
            .as_ref()
            .map(r2sym::SemanticArtifact::semantic_claim_summary)
            .map(|claims| r2sym::ProofCoverage::from_semantic_claims(&claims))
            .unwrap_or_default();
        Self {
            types,
            semantics,
            proof,
            decompile_route: None,
            input_quality: None,
            callee_resolution: CalleeResolutionFacts::default(),
            callsites: FunctionCallsiteFacts::default(),
            call_results: FunctionCallResultFacts::default(),
            call_render: FunctionCallRenderFacts::default(),
            control: FunctionControlFacts::default(),
            render: FunctionRenderFacts::default(),
            assumptions: r2ssa::AssumptionSet::default(),
            plans,
            summary_view: InterprocSummaryView::default(),
            diagnostics: Vec::new(),
            assumption_usage: r2ssa::AssumptionUsageReport::default(),
        }
    }

    pub fn with_assumptions(mut self, assumptions: r2ssa::AssumptionSet) -> Self {
        self.assumptions = assumptions;
        self
    }

    pub fn with_summary_set(mut self, set: Option<r2ssa::InterprocSummarySet>) -> Self {
        self.summary_view = InterprocSummaryView::new(set);
        self
    }

    pub fn set_summary_set(&mut self, set: Option<r2ssa::InterprocSummarySet>) {
        self.summary_view = InterprocSummaryView::new(set);
    }

    pub fn with_summary_view(mut self, summary_view: InterprocSummaryView) -> Self {
        self.summary_view = summary_view;
        self
    }

    pub fn set_summary_view(&mut self, summary_view: InterprocSummaryView) {
        self.summary_view = summary_view;
    }

    pub fn with_diagnostics<I>(mut self, diagnostics: I) -> Self
    where
        I: IntoIterator<Item = String>,
    {
        self.diagnostics = diagnostics.into_iter().collect();
        self
    }

    pub fn with_assumption_usage(mut self, usage: r2ssa::AssumptionUsageReport) -> Self {
        self.assumption_usage = usage;
        self
    }

    pub fn merge_assumption_usage(&mut self, usage: &r2ssa::AssumptionUsageReport) {
        self.assumption_usage.extend(usage);
    }

    pub fn with_proof_coverage(mut self, proof: r2sym::ProofCoverage) -> Self {
        self.proof = proof;
        self
    }

    pub fn with_decompile_route(mut self, route: DecompileRouteFacts) -> Self {
        self.decompile_route = Some(route);
        self
    }

    pub fn with_input_quality(mut self, input_quality: FunctionInputQualityFacts) -> Self {
        self.input_quality = Some(input_quality);
        self
    }

    pub fn set_input_quality(&mut self, input_quality: Option<FunctionInputQualityFacts>) {
        self.input_quality = input_quality;
    }

    pub fn input_quality(&self) -> Option<&FunctionInputQualityFacts> {
        self.input_quality.as_ref()
    }

    pub fn with_callee_resolution(mut self, callee_resolution: CalleeResolutionFacts) -> Self {
        self.callee_resolution = callee_resolution;
        self
    }

    pub fn set_callee_resolution(&mut self, callee_resolution: CalleeResolutionFacts) {
        self.callee_resolution = callee_resolution;
    }

    pub fn callee_resolution(&self) -> Option<&CalleeResolutionFacts> {
        (!self.callee_resolution.is_empty()).then_some(&self.callee_resolution)
    }

    pub fn with_callsites(mut self, callsites: FunctionCallsiteFacts) -> Self {
        self.callsites = callsites;
        self
    }

    pub fn set_callsites(&mut self, callsites: FunctionCallsiteFacts) {
        self.callsites = callsites;
    }

    pub fn callsites(&self) -> Option<&FunctionCallsiteFacts> {
        (!self.callsites.is_empty()).then_some(&self.callsites)
    }

    pub fn with_call_results(mut self, call_results: FunctionCallResultFacts) -> Self {
        self.call_results = call_results;
        self
    }

    pub fn set_call_results(&mut self, call_results: FunctionCallResultFacts) {
        self.call_results = call_results;
    }

    pub fn call_results(&self) -> Option<&FunctionCallResultFacts> {
        (!self.call_results.is_empty()).then_some(&self.call_results)
    }

    pub fn with_call_render(mut self, call_render: FunctionCallRenderFacts) -> Self {
        self.call_render = call_render;
        self
    }

    pub fn set_call_render(&mut self, call_render: FunctionCallRenderFacts) {
        self.call_render = call_render;
    }

    pub fn call_render(&self) -> Option<&FunctionCallRenderFacts> {
        (!self.call_render.is_empty()).then_some(&self.call_render)
    }

    pub fn with_control(mut self, control: FunctionControlFacts) -> Self {
        self.control = control;
        self
    }

    pub fn set_control(&mut self, control: FunctionControlFacts) {
        self.control = control;
    }

    pub fn control(&self) -> Option<&FunctionControlFacts> {
        (!self.control.is_empty()).then_some(&self.control)
    }

    pub fn with_render(mut self, render: FunctionRenderFacts) -> Self {
        self.render = render;
        self
    }

    pub fn set_render(&mut self, render: FunctionRenderFacts) {
        self.render = render;
    }

    pub fn render(&self) -> Option<&FunctionRenderFacts> {
        (!self.render.is_empty()).then_some(&self.render)
    }

    pub fn render_facts(&self) -> &FunctionRenderFacts {
        &self.render
    }

    pub fn control_facts(&self) -> &FunctionControlFacts {
        &self.control
    }

    pub fn authorized_stack_slot_owner_render(
        &self,
        object: r2ssa::ObjectId,
        offset: i64,
        name: &str,
    ) -> Option<StackSlotOwnerRenderAuthorization> {
        let name = name.trim();
        if name.is_empty() {
            return None;
        }
        let render_offset = self.render.stack_slot_offsets.get(&object).copied()?;
        if render_offset != offset || !self.stack_owner_name_is_renderable(offset, name) {
            return None;
        }
        Some(StackSlotOwnerRenderAuthorization {
            object,
            offset,
            name: name.to_string(),
        })
    }

    pub fn authorized_stack_slot_owner_render_by_offset(
        &self,
        offset: i64,
        name: &str,
    ) -> Option<StackSlotOwnerRenderAuthorization> {
        let mut matching_objects = self
            .render
            .stack_slot_offsets
            .iter()
            .filter_map(|(object, slot_offset)| (*slot_offset == offset).then_some(*object));
        let object = matching_objects.next()?;
        if matching_objects.next().is_some() {
            return None;
        }
        self.authorized_stack_slot_owner_render(object, offset, name)
    }

    pub fn authorized_stack_param_owner_render(
        &self,
        object: r2ssa::ObjectId,
        offset: i64,
    ) -> Option<StackSlotOwnerRenderAuthorization> {
        let render_offset = self.render.stack_slot_offsets.get(&object).copied()?;
        if render_offset != offset {
            return None;
        }
        if let Some(name) = self.stack_param_owner_name_for_offset(offset) {
            return self.authorized_stack_slot_owner_render(object, offset, &name);
        }
        None
    }

    fn stack_param_owner_name_for_offset(&self, offset: i64) -> Option<String> {
        let mut candidate = None;
        for (slot_key, slot) in &self.types.stack_slots {
            if stack_slot_matches_offset(slot_key, offset)
                && matches!(
                    slot.role,
                    ExternalStackSlotRole::StackArg | ExternalStackSlotRole::ParamHome
                )
            {
                if let Some(name) = slot
                    .param_name
                    .as_ref()
                    .filter(|name| !name.trim().is_empty())
                    .filter(|name| {
                        slot.ty.as_ref().is_some_and(stack_owner_type_is_renderable)
                            || (matches!(slot.role, ExternalStackSlotRole::ParamHome)
                                && signature_param_name_type_is_renderable(
                                    self.types.merged_signature.as_ref(),
                                    name,
                                ))
                    })
                {
                    remember_stack_param_owner_name(&mut candidate, name)?;
                    continue;
                }
                if !slot.name.trim().is_empty() {
                    remember_stack_param_owner_name(&mut candidate, &slot.name)?;
                }
            }
        }
        if candidate.is_some() {
            return candidate;
        }

        for binding in &self.types.visible_bindings {
            let Some(slot) = binding.stack_slot.as_ref() else {
                continue;
            };
            if stack_slot_matches_offset(slot, offset)
                && matches!(binding.kind, VisibleBindingKind::Param)
                && binding
                    .ty
                    .as_ref()
                    .is_some_and(stack_owner_type_is_renderable)
                && !binding.name.trim().is_empty()
            {
                remember_stack_param_owner_name(&mut candidate, &binding.name)?;
            }
        }
        candidate
    }

    fn stack_owner_name_is_renderable(&self, offset: i64, name: &str) -> bool {
        self.types.visible_bindings.iter().any(|binding| {
            let Some(slot) = binding.stack_slot.as_ref() else {
                return false;
            };
            binding.name.eq_ignore_ascii_case(name)
                && stack_slot_matches_offset(slot, offset)
                && binding
                    .ty
                    .as_ref()
                    .is_some_and(stack_owner_type_is_renderable)
                && visible_stack_binding_kind_is_renderable(&binding.kind)
        }) || self.types.stack_slots.iter().any(|(slot_key, slot)| {
            (slot.name.eq_ignore_ascii_case(name)
                || (matches!(
                    slot.role,
                    ExternalStackSlotRole::StackArg | ExternalStackSlotRole::ParamHome
                ) && slot
                    .param_name
                    .as_ref()
                    .is_some_and(|param_name| param_name.eq_ignore_ascii_case(name))))
                && stack_slot_matches_offset(slot_key, offset)
                && (slot.ty.as_ref().is_some_and(stack_owner_type_is_renderable)
                    || (matches!(slot.role, ExternalStackSlotRole::ParamHome)
                        && slot.param_name.as_ref().is_some_and(|param_name| {
                            param_name.eq_ignore_ascii_case(name)
                                && signature_param_name_type_is_renderable(
                                    self.types.merged_signature.as_ref(),
                                    param_name,
                                )
                        })))
                && (external_stack_slot_role_is_renderable(slot.role)
                    || (matches!(slot.role, ExternalStackSlotRole::ParamHome)
                        && slot
                            .param_name
                            .as_ref()
                            .is_some_and(|param_name| param_name.eq_ignore_ascii_case(name))))
        })
    }

    pub fn authorized_recovered_stack_slot_owner_render(
        &self,
        object: r2ssa::ObjectId,
        offset: i64,
        name: &str,
    ) -> Option<StackSlotOwnerRenderAuthorization> {
        let name = name.trim();
        if !recovered_stack_owner_name_is_renderable(name) {
            return None;
        }
        let render_offset = self.render.stack_slot_offsets.get(&object).copied()?;
        if render_offset != offset {
            return None;
        }
        Some(StackSlotOwnerRenderAuthorization {
            object,
            offset,
            name: name.to_string(),
        })
    }

    pub fn set_decompile_route(&mut self, route: Option<DecompileRouteFacts>) {
        self.decompile_route = route;
    }

    pub fn decompile_route(&self) -> Option<&DecompileRouteFacts> {
        self.decompile_route.as_ref()
    }

    pub fn proof_coverage(&self) -> &r2sym::ProofCoverage {
        &self.proof
    }

    pub fn decompile_fallback_comment(&self) -> Option<&str> {
        self.decompile_route
            .as_ref()
            .filter(|route| route.kind == DecompileRouteKind::FallbackComment)
            .and_then(|route| {
                route
                    .fallback_comment
                    .as_deref()
                    .or(route.reason.as_deref())
            })
    }

    pub fn merge_proof_coverage(&mut self, proof: r2sym::ProofCoverage) {
        self.proof = std::mem::take(&mut self.proof).merge(proof);
    }

    pub fn set_semantics(&mut self, semantics: Option<r2sym::SemanticArtifact>) {
        self.semantics = semantics;
        self.refresh_plans();
        if let Some(semantics) = self.semantics.as_ref() {
            self.merge_proof_coverage(r2sym::ProofCoverage::from_semantic_claims(
                &semantics.semantic_claim_summary(),
            ));
        }
    }

    pub fn refresh_plans(&mut self) {
        self.plans = AnalysisPlans::from_semantics(self.semantics.as_ref());
    }

    pub fn canonicalize_type_facts(&mut self) {
        self.types = std::mem::take(&mut self.types).canonicalized();
        self.refresh_plans();
    }

    pub fn replace_type_facts(&mut self, types: FunctionTypeFacts) {
        self.types = types.canonicalized();
        self.refresh_plans();
    }

    pub fn normalize_field_certificates_from_external_layout(&mut self) {
        let Some(signature) = self.types.merged_signature.as_ref() else {
            return;
        };
        let type_db = &self.types.external_type_db;
        if type_db.structs.is_empty() {
            return;
        }

        for cert in &mut self.types.field_access_certificates {
            let Some(param) = signature.params.get(cert.slot) else {
                continue;
            };
            let Some(struct_name) = struct_name_from_pointer_type(param.ty.as_ref()) else {
                continue;
            };
            let key = normalize_external_type_name(struct_name).to_ascii_lowercase();
            let Some(field) = type_db
                .structs
                .get(&key)
                .and_then(|structure| structure.fields.get(&cert.field_offset))
            else {
                continue;
            };
            cert.field_name = field.name.clone();
            if cert.field_type.is_none() {
                cert.field_type = field.ty.clone();
            }
        }
    }

    pub fn populate_member_access_render_facts_from_field_certificates(
        &mut self,
        prepared: &r2ssa::SsaArtifact,
        param_slots: &ParamSlotResolver,
    ) {
        if self.types.field_access_certificates.is_empty() {
            return;
        }

        let mut member_facts = Vec::new();
        for memory in self.render.memory_accesses.values() {
            if memory.width == 0 {
                continue;
            }
            let Some(field_offset) = prepared_memory_access_field_offset(prepared, memory) else {
                continue;
            };
            let param_slot = prepared_memory_access_param_slot(prepared, memory, param_slots);
            let ptr_bits = prepared_memory_access_ptr_bits(prepared, memory);
            member_facts.extend(self.member_render_facts_for_memory(
                memory,
                field_offset,
                ptr_bits,
                param_slot,
            ));
        }

        for candidate in self.types.scalar_array_render_candidates.iter().copied() {
            if candidate.access_width == 0
                || !self.scalar_array_render_candidate_has_array_certificate(candidate)
            {
                continue;
            }
            let key = (candidate.block_addr, candidate.op_index, candidate.is_write);
            let Some(accesses) = self.render.memory_accesses_by_op.get(&key) else {
                continue;
            };
            for access in accesses {
                let Some(memory) = self.render.memory_accesses.get(access) else {
                    continue;
                };
                if memory.block_addr != candidate.block_addr
                    || memory.op_index != candidate.op_index
                    || memory.is_write != candidate.is_write
                    || memory.width == 0
                    || memory.width != candidate.access_width
                {
                    continue;
                }
                let prepared_param_slot =
                    prepared_memory_access_param_slot(prepared, memory, param_slots);
                if prepared_param_slot.is_some_and(|slot| slot != candidate.slot) {
                    continue;
                }
                let ptr_bits = prepared_memory_access_ptr_bits(prepared, memory);
                member_facts.extend(self.member_render_facts_for_memory(
                    memory,
                    candidate.field_offset,
                    ptr_bits,
                    Some(candidate.slot),
                ));
            }
        }

        for fact in member_facts {
            let key = (fact.block_addr, fact.op_index, fact.is_write);
            let facts = self.render.member_accesses_by_op.entry(key).or_default();
            if !facts.contains(&fact) {
                facts.push(fact);
            }
        }

        for facts in self.render.member_accesses_by_op.values_mut() {
            facts.sort_by(|a, b| {
                (
                    a.block_addr,
                    a.op_index,
                    a.is_write,
                    a.field_offset,
                    a.access_width,
                    a.field_name.as_str(),
                    a.access,
                )
                    .cmp(&(
                        b.block_addr,
                        b.op_index,
                        b.is_write,
                        b.field_offset,
                        b.access_width,
                        b.field_name.as_str(),
                        b.access,
                    ))
            });
        }
    }

    fn member_render_facts_for_memory(
        &self,
        memory: &MemoryAccessRenderFact,
        field_offset: u64,
        ptr_bits: u32,
        param_slot: Option<usize>,
    ) -> Vec<MemberAccessRenderFact> {
        self.types
            .field_access_certificates
            .iter()
            .filter(|cert| {
                param_slot == Some(cert.slot)
                    && cert.field_offset == field_offset
                    && field_certificate_width_matches(cert, memory.width, ptr_bits)
            })
            .map(|cert| MemberAccessRenderFact {
                access: memory.access,
                block_addr: memory.block_addr,
                op_index: memory.op_index,
                object: memory.object,
                is_write: memory.is_write,
                field_offset,
                field_name: cert.field_name.clone(),
                access_width: memory.width,
            })
            .collect()
    }

    pub fn populate_array_access_render_facts_from_scalar_candidates(
        &mut self,
        prepared: &r2ssa::SsaArtifact,
        param_slots: &ParamSlotResolver,
    ) {
        if self.types.scalar_array_render_candidates.is_empty() {
            return;
        }

        for candidate in self.types.scalar_array_render_candidates.iter().copied() {
            if candidate.element_stride == 0
                || candidate.access_width == 0
                || !self.scalar_array_render_candidate_has_array_certificate(candidate)
            {
                continue;
            }
            let key = (candidate.block_addr, candidate.op_index, candidate.is_write);
            let Some(accesses) = self.render.memory_accesses_by_op.get(&key) else {
                continue;
            };
            let accesses = accesses.clone();
            for access in accesses {
                let Some(memory) = self.render.memory_accesses.get(&access) else {
                    continue;
                };
                if memory.block_addr != candidate.block_addr
                    || memory.op_index != candidate.op_index
                    || memory.is_write != candidate.is_write
                    || memory.width == 0
                    || memory.width != candidate.access_width
                {
                    continue;
                }
                let prepared_param_slot =
                    prepared_memory_access_param_slot(prepared, memory, param_slots);
                if prepared_param_slot.is_some_and(|slot| slot != candidate.slot) {
                    continue;
                }
                let fact = ArrayAccessRenderFact {
                    access,
                    block_addr: memory.block_addr,
                    op_index: memory.op_index,
                    object: memory.object,
                    is_write: memory.is_write,
                    field_offset: candidate.field_offset,
                    element_stride: candidate.element_stride,
                    access_width: memory.width,
                };
                let facts = self.render.array_accesses_by_op.entry(key).or_default();
                if !facts.contains(&fact) {
                    facts.push(fact);
                }
            }
        }

        for facts in self.render.array_accesses_by_op.values_mut() {
            facts.sort_by_key(|fact| {
                (
                    fact.block_addr,
                    fact.op_index,
                    fact.is_write,
                    fact.field_offset,
                    fact.element_stride,
                    fact.access_width,
                    fact.access,
                    fact.object,
                )
            });
        }
    }

    fn scalar_array_render_candidate_has_array_certificate(
        &self,
        candidate: crate::facts::ScalarArrayRenderCandidate,
    ) -> bool {
        self.types.array_index_certificates.iter().any(|cert| {
            cert.slot == candidate.slot
                && cert.field_offset == candidate.field_offset
                && cert.element_stride == candidate.element_stride
                && match &cert.base {
                    Some(crate::facts::ArrayIndexBase::Param { index }) => *index == candidate.slot,
                    Some(crate::facts::ArrayIndexBase::StackSlot { .. }) | None => true,
                }
        })
    }

    pub fn type_facts(&self) -> &FunctionTypeFacts {
        &self.types
    }

    #[doc(hidden)]
    pub fn __test_type_facts_mut(&mut self) -> &mut FunctionTypeFacts {
        &mut self.types
    }

    #[doc(hidden)]
    pub fn __test_render_facts_mut(&mut self) -> &mut FunctionRenderFacts {
        &mut self.render
    }

    pub fn assumptions(&self) -> &r2ssa::AssumptionSet {
        &self.assumptions
    }

    pub fn plans(&self) -> &AnalysisPlans {
        &self.plans
    }

    pub fn summary_view(&self) -> &InterprocSummaryView {
        &self.summary_view
    }

    pub fn diagnostics(&self) -> &[String] {
        &self.diagnostics
    }

    pub fn assumption_usage(&self) -> &r2ssa::AssumptionUsageReport {
        &self.assumption_usage
    }

    pub fn type_plan(&self) -> Option<r2sym::TypePlan> {
        self.plans.type_plan.clone()
    }

    pub fn decompile_plan(&self) -> Option<r2sym::DecompilePlan> {
        self.plans.decompile.clone()
    }

    pub fn query_plan(&self) -> Option<r2sym::QueryPlan> {
        self.plans.query.clone()
    }

    pub fn artifact_build_plan(&self) -> Option<r2sym::ArtifactBuildPlan> {
        self.plans.artifact_build.clone()
    }

    pub fn apply_signature_projection(
        &mut self,
        function_name: &str,
        projection: FunctionSignatureProjection,
        ptr_bits: u32,
    ) -> SignatureProjectionResult {
        self.types
            .apply_signature_projection(function_name, projection, ptr_bits)
    }

    pub fn apply_decompile_type_override(&mut self, override_facts: FunctionTypeFacts) -> bool {
        let Some(signature) = override_facts.render_authorized_signature().cloned() else {
            return false;
        };
        self.types.merged_signature = Some(signature);
        self.types.signature_certificate = override_facts.signature_certificate;
        true
    }

    pub fn attach_prepared_decompile_evidence(&mut self, prepared: &r2ssa::SsaArtifact) {
        let prepared_callee_resolution = prepared_callee_resolution_facts(prepared, self);
        let prepared_callsites = prepared_callsite_argument_facts(prepared);
        let prepared_call_results = prepared_call_result_facts(prepared);
        let prepared_call_render = prepared_call_render_facts(prepared, &prepared_call_results);
        let prepared_control = prepared_control_facts(prepared);
        let prepared_render = prepared_render_facts(prepared);

        merge_callee_resolution_facts(&mut self.callee_resolution, prepared_callee_resolution);
        merge_callsite_facts(&mut self.callsites, prepared_callsites);
        merge_call_result_facts(&mut self.call_results, prepared_call_results);
        merge_call_render_facts(&mut self.call_render, prepared_call_render);
        merge_control_facts(&mut self.control, prepared_control);
        merge_render_facts(&mut self.render, prepared_render);
    }

    pub fn interproc_summary_set(&self) -> Option<&r2ssa::InterprocSummarySet> {
        self.summary_view.as_set()
    }

    pub fn semantic_artifact(&self) -> Option<&r2sym::SemanticArtifact> {
        self.semantics.as_ref()
    }

    pub fn summary_rollup(&self) -> Option<&SummaryEffectRollup> {
        self.summary_view.rollup.as_ref()
    }

    #[doc(hidden)]
    pub fn __test_set_summary_rollup(&mut self, rollup: SummaryEffectRollup) {
        self.summary_view.rollup = Some(rollup);
    }

    pub fn has_assumption_conflicts(&self) -> bool {
        !self.assumption_usage.conflicts.is_empty()
    }

    pub fn has_applied_assumptions(&self) -> bool {
        !self.assumption_usage.applied.is_empty()
    }

    pub fn has_summary_conflicts(&self) -> bool {
        self.summary_view
            .diagnostics()
            .is_some_and(|diagnostics| !diagnostics.converged)
    }

    pub fn decompile_capability(&self) -> DecompileCapabilityView {
        let mut capability = DecompileCapabilityView {
            plan: self.decompile_plan(),
            assumption_conflicted: self.has_assumption_conflicts(),
            summary_conflicted: self.has_summary_conflicts(),
            ..DecompileCapabilityView::default()
        };
        let Some(semantics) = self.semantic_artifact() else {
            return capability;
        };
        capability.slice_class = semantics.slice_class();
        capability.skipped_large_cfg = semantics.diagnostics.skipped_large_cfg;
        capability.has_native_regions = semantics
            .native_body()
            .is_some_and(|body| !body.regions.is_empty());
        capability.has_summary_islands = semantics
            .native_body()
            .is_some_and(r2sym::NativeArtifactBody::has_summary_islands);
        capability.has_primary_summary_islands = semantics
            .native_body()
            .is_some_and(r2sym::NativeArtifactBody::has_primary_summary_islands);
        capability.summary_island_count = semantics
            .native_body()
            .map(r2sym::NativeArtifactBody::summary_island_count)
            .unwrap_or(0);
        capability.primary_summary_island_count = semantics
            .native_body()
            .map(r2sym::NativeArtifactBody::primary_summary_island_count)
            .unwrap_or(0);
        capability.generic_memory_summary_count = semantics
            .native_body()
            .map(r2sym::NativeArtifactBody::generic_memory_summary_count)
            .unwrap_or(0);
        capability.has_memory_read_write_summary_pair = semantics
            .native_body()
            .is_some_and(r2sym::NativeArtifactBody::has_memory_read_write_summary_pair);
        capability.actionable_region_count = semantics.actionable_regions().len();
        capability.ambiguous_targets = semantics.ambiguous_targets();
        capability.residual_reasons = semantics.diagnostics.residual_reasons.clone();
        capability
    }
}

fn struct_name_from_pointer_type(ty: Option<&CTypeLike>) -> Option<&str> {
    let CTypeLike::Pointer(inner) = ty? else {
        return None;
    };
    match inner.as_ref() {
        CTypeLike::Struct(name) | CTypeLike::Typedef(name) => Some(name),
        _ => None,
    }
}

fn prepared_callee_resolution_facts(
    prepared: &r2ssa::SsaArtifact,
    function_facts: &FunctionFacts,
) -> CalleeResolutionFacts {
    let type_facts = function_facts.types.clone().canonicalized();
    let known_function_signatures = type_facts
        .known_function_signatures
        .iter()
        .map(|(name, ty)| (crate::normalize_callee_name(name), ty.clone()))
        .collect::<HashMap<_, _>>();
    let function_names = HashMap::new();
    let symbols = HashMap::new();
    let ctx = CalleeIdentityContext {
        function_names: &function_names,
        symbols: &symbols,
        callee_facts: &type_facts.callee_facts,
        known_function_signatures: &known_function_signatures,
    };

    CalleeResolutionFacts::from_direct_call_targets(
        prepared
            .call_sites()
            .by_id
            .values()
            .filter_map(|call_site| {
                let direct_target = prepared.resolved_call_target(call_site)?;
                let (block_addr, op_index) = prepared.inst_op_site(call_site.at)?;
                Some((
                    CallsiteKey {
                        block_addr,
                        op_index,
                    },
                    direct_target,
                ))
            }),
        &ctx,
    )
}

fn merge_callee_resolution_facts(
    existing: &mut CalleeResolutionFacts,
    prepared: CalleeResolutionFacts,
) {
    for (key, identity) in prepared.by_key {
        existing.by_key.entry(key).or_insert(identity);
    }
    for (addr, key) in prepared.by_direct_addr {
        existing.by_direct_addr.entry(addr).or_insert(key);
    }
    for (callsite, key) in prepared.by_callsite {
        existing.by_callsite.entry(callsite).or_insert(key);
    }
    for (name, key) in prepared.by_name {
        existing.by_name.entry(name).or_insert(key);
    }
}

fn merge_callsite_facts(existing: &mut FunctionCallsiteFacts, prepared: FunctionCallsiteFacts) {
    for (callsite, facts) in prepared.by_callsite {
        existing.by_callsite.entry(callsite).or_insert(facts);
    }
}

fn merge_call_result_facts(
    existing: &mut FunctionCallResultFacts,
    prepared: FunctionCallResultFacts,
) {
    for (value, fact) in prepared.by_value {
        existing.by_value.entry(value).or_insert(fact);
    }
    for (callsite, values) in prepared.by_callsite {
        let existing_values = existing.by_callsite.entry(callsite).or_default();
        for value in values {
            if !existing_values.contains(&value) {
                existing_values.push(value);
            }
        }
    }
}

fn merge_call_render_facts(
    existing: &mut FunctionCallRenderFacts,
    prepared: FunctionCallRenderFacts,
) {
    for (callsite, fact) in prepared.by_callsite {
        existing.by_callsite.entry(callsite).or_insert(fact);
    }
}

fn merge_control_facts(existing: &mut FunctionControlFacts, prepared: FunctionControlFacts) {
    for (block, fact) in prepared.branch_predicates {
        existing.branch_predicates.entry(block).or_insert(fact);
    }
    for (block, assumptions) in prepared.block_assumptions {
        let existing_assumptions = existing.block_assumptions.entry(block).or_default();
        for assumption in assumptions {
            if !existing_assumptions.contains(&assumption) {
                existing_assumptions.push(assumption);
            }
        }
    }
    for (loop_id, fact) in prepared.loops {
        existing.loops.entry(loop_id).or_insert(fact);
    }
    for (block, fact) in prepared.switches {
        existing.switches.entry(block).or_insert(fact);
    }
}

fn merge_render_facts(existing: &mut FunctionRenderFacts, prepared: FunctionRenderFacts) {
    for (value, fact) in prepared.expressions {
        existing.expressions.entry(value).or_insert(fact);
    }
    for (value, fact) in prepared.string_literals_by_value {
        existing
            .string_literals_by_value
            .entry(value)
            .or_insert(fact);
    }
    for (access, fact) in prepared.memory_accesses {
        existing.memory_accesses.entry(access).or_insert(fact);
    }
    for (op, accesses) in prepared.memory_accesses_by_op {
        let existing_accesses = existing.memory_accesses_by_op.entry(op).or_default();
        for access in accesses {
            if !existing_accesses.contains(&access) {
                existing_accesses.push(access);
            }
        }
    }
    for (op, facts) in prepared.member_accesses_by_op {
        let existing_facts = existing.member_accesses_by_op.entry(op).or_default();
        for fact in facts {
            if !existing_facts.contains(&fact) {
                existing_facts.push(fact);
            }
        }
    }
    for (op, facts) in prepared.array_accesses_by_op {
        let existing_facts = existing.array_accesses_by_op.entry(op).or_default();
        for fact in facts {
            if !existing_facts.contains(&fact) {
                existing_facts.push(fact);
            }
        }
    }
    for (op, fact) in prepared.returns_by_op {
        existing.returns_by_op.entry(op).or_insert(fact);
    }
    for (object, offset) in prepared.stack_slot_offsets {
        existing.stack_slot_offsets.entry(object).or_insert(offset);
    }
}

fn prepared_callsite_argument_facts(prepared: &r2ssa::SsaArtifact) -> FunctionCallsiteFacts {
    let by_callsite = prepared
        .certificates()
        .callsites
        .values()
        .filter_map(|cert| {
            let (block_addr, op_index) = prepared.inst_op_site(cert.at)?;
            let callsite = CallsiteKey {
                block_addr,
                op_index,
            };
            let argument_values = cert
                .argument_values
                .iter()
                .copied()
                .enumerate()
                .map(|(index, value)| CallArgumentValueFact { index, value })
                .collect();
            let register_argument_locations = cert
                .argument_certificates
                .iter()
                .filter_map(|argument| {
                    let r2ssa::CallArgumentLocation::Register { name } = &argument.location else {
                        return None;
                    };
                    Some(RegisterCallArgumentLocationFact {
                        index: argument.index,
                        value: argument.value,
                        name: name.clone(),
                        source_inst: argument.source_inst,
                    })
                })
                .collect();
            let stack_argument_locations = cert
                .argument_certificates
                .iter()
                .filter_map(|argument| {
                    let r2ssa::CallArgumentLocation::Stack {
                        object,
                        offset,
                        memory_access,
                    } = argument.location
                    else {
                        return None;
                    };
                    Some(StackCallArgumentLocationFact {
                        index: argument.index,
                        value: argument.value,
                        object,
                        offset,
                        memory_access,
                        source_inst: argument.source_inst,
                    })
                })
                .collect();
            Some((
                callsite,
                CallsiteArgumentFacts {
                    callsite,
                    call_site_id: cert.call_site,
                    at: cert.at,
                    target: cert.target,
                    direct_target: cert.direct_target,
                    argument_values,
                    register_argument_locations,
                    stack_argument_locations,
                },
            ))
        })
        .collect();
    FunctionCallsiteFacts { by_callsite }
}

fn prepared_call_result_facts(prepared: &r2ssa::SsaArtifact) -> FunctionCallResultFacts {
    let mut by_value = BTreeMap::new();
    let mut by_callsite = BTreeMap::<CallsiteKey, Vec<r2ssa::ValueId>>::new();
    for cert in prepared.certificates().call_results.values() {
        let Some(callsite_cert) = prepared.certificates().callsites.get(&cert.call_site) else {
            continue;
        };
        let callsite = CallsiteKey {
            block_addr: callsite_cert.block_addr,
            op_index: callsite_cert.op_index,
        };
        by_callsite.entry(callsite).or_default().push(cert.value);
        by_value.insert(
            cert.value,
            CallResultFact {
                callsite,
                call_site_id: cert.call_site,
                at: cert.at,
                value: cert.value,
                width: cert.width,
                carrier: cert.carrier.clone(),
                owner: cert.owner.clone(),
            },
        );
    }
    FunctionCallResultFacts {
        by_value,
        by_callsite,
    }
}

fn prepared_call_render_facts(
    prepared: &r2ssa::SsaArtifact,
    call_results: &FunctionCallResultFacts,
) -> FunctionCallRenderFacts {
    let by_callsite = prepared
        .certificates()
        .callsites
        .values()
        .map(|cert| {
            let callsite = CallsiteKey {
                block_addr: cert.block_addr,
                op_index: cert.op_index,
            };
            let disposition = if call_results
                .results_for_site(callsite)
                .any(|result| matches!(result.owner, Some(r2ssa::ValueOwner::StackSlot { .. })))
            {
                CallsiteRenderDisposition::AssignedResult
            } else {
                CallsiteRenderDisposition::SideEffectStatement
            };
            (
                callsite,
                CallsiteRenderFact {
                    callsite,
                    target: Some(cert.target),
                    disposition,
                    proof_values: cert.argument_values.clone(),
                    residual_reason: None,
                },
            )
        })
        .collect();
    FunctionCallRenderFacts { by_callsite }
}

fn prepared_memory_access_field_offset(
    prepared: &r2ssa::SsaArtifact,
    memory: &MemoryAccessRenderFact,
) -> Option<u64> {
    let offset = prepared_address_base_offset(prepared, memory.address, 0)?;
    u64::try_from(offset).ok()
}

fn prepared_memory_access_param_slot(
    prepared: &r2ssa::SsaArtifact,
    memory: &MemoryAccessRenderFact,
    param_slots: &ParamSlotResolver,
) -> Option<usize> {
    prepared_address_base_param_slot(prepared, memory.address, param_slots, 0)
}

fn prepared_memory_access_ptr_bits(
    prepared: &r2ssa::SsaArtifact,
    memory: &MemoryAccessRenderFact,
) -> u32 {
    prepared
        .graph()
        .value(memory.address)
        .map(|value| value.var.size.saturating_mul(8))
        .filter(|bits| *bits > 0)
        .unwrap_or(64)
}

fn prepared_address_base_offset(
    prepared: &r2ssa::SsaArtifact,
    value: r2ssa::ValueId,
    depth: usize,
) -> Option<i64> {
    if depth > 8 {
        return None;
    }
    let graph = prepared.graph();
    let var = &graph.value(value)?.var;
    if const_var_i64(var).is_some() {
        return None;
    }
    if prepared
        .stack_reload_certificate_for_value(value)
        .and_then(|reload| graph.value(reload.canonical_source))
        .is_some_and(|source| source.var.version == 0 && source.var.is_register())
    {
        return Some(0);
    }
    let Some(def_inst) = graph.def_inst(value) else {
        return Some(0);
    };
    let inst = graph.inst(def_inst)?;
    let r2ssa::InstPayload::Op(op) = &inst.payload else {
        return None;
    };
    match op {
        r2ssa::SSAOp::Copy { src, .. }
        | r2ssa::SSAOp::New { src, .. }
        | r2ssa::SSAOp::Cast { src, .. }
        | r2ssa::SSAOp::Subpiece { src, .. }
        | r2ssa::SSAOp::IntZExt { src, .. }
        | r2ssa::SSAOp::IntSExt { src, .. } => prepared_var_base_offset(prepared, src, depth + 1),
        r2ssa::SSAOp::IntAdd { a, b, .. } => {
            prepared_binary_const_offset(prepared, a, b, depth + 1, 1)
        }
        r2ssa::SSAOp::IntSub { a, b, .. } => {
            prepared_binary_const_offset(prepared, a, b, depth + 1, -1)
        }
        r2ssa::SSAOp::PtrAdd {
            base,
            index,
            element_size,
            ..
        } => {
            let delta = const_var_i64(index)?.checked_mul(i64::from(*element_size))?;
            prepared_var_base_offset(prepared, base, depth + 1)?.checked_add(delta)
        }
        r2ssa::SSAOp::PtrSub {
            base,
            index,
            element_size,
            ..
        } => {
            let delta = const_var_i64(index)?.checked_mul(i64::from(*element_size))?;
            prepared_var_base_offset(prepared, base, depth + 1)?.checked_sub(delta)
        }
        _ => None,
    }
}

fn prepared_var_base_offset(
    prepared: &r2ssa::SsaArtifact,
    var: &r2ssa::SSAVar,
    depth: usize,
) -> Option<i64> {
    let value = prepared.graph().value_id_for_var(var)?;
    prepared_address_base_offset(prepared, value, depth)
}

fn prepared_binary_const_offset(
    prepared: &r2ssa::SsaArtifact,
    a: &r2ssa::SSAVar,
    b: &r2ssa::SSAVar,
    depth: usize,
    rhs_sign: i64,
) -> Option<i64> {
    match (const_var_i64(a), const_var_i64(b)) {
        (None, Some(rhs)) => {
            let delta = rhs.checked_mul(rhs_sign)?;
            prepared_var_base_offset(prepared, a, depth)?.checked_add(delta)
        }
        (Some(lhs), None) if rhs_sign == 1 => {
            prepared_var_base_offset(prepared, b, depth)?.checked_add(lhs)
        }
        _ => None,
    }
}

fn prepared_address_base_param_slot(
    prepared: &r2ssa::SsaArtifact,
    value: r2ssa::ValueId,
    param_slots: &ParamSlotResolver,
    depth: usize,
) -> Option<usize> {
    if depth > 8 {
        return None;
    }
    let graph = prepared.graph();
    let var = &graph.value(value)?.var;
    if const_var_i64(var).is_some() {
        return None;
    }
    if let Some(source) = prepared
        .stack_reload_certificate_for_value(value)
        .and_then(|reload| graph.value(reload.canonical_source))
        && source.var.version == 0
    {
        return param_slots.slot_for_var(&source.var);
    }
    let Some(def_inst) = graph.def_inst(value) else {
        return param_slots.slot_for_var(var);
    };
    let inst = graph.inst(def_inst)?;
    let r2ssa::InstPayload::Op(op) = &inst.payload else {
        return None;
    };
    match op {
        r2ssa::SSAOp::Copy { src, .. }
        | r2ssa::SSAOp::New { src, .. }
        | r2ssa::SSAOp::Cast { src, .. }
        | r2ssa::SSAOp::Subpiece { src, .. }
        | r2ssa::SSAOp::IntZExt { src, .. }
        | r2ssa::SSAOp::IntSExt { src, .. } => {
            prepared_var_base_param_slot(prepared, src, param_slots, depth + 1)
        }
        r2ssa::SSAOp::IntAdd { a, b, .. } => {
            prepared_add_param_slot(prepared, a, b, param_slots, depth + 1)
        }
        r2ssa::SSAOp::IntSub { a, b, .. } => {
            prepared_sub_param_slot(prepared, a, b, param_slots, depth + 1)
        }
        r2ssa::SSAOp::PtrAdd { base, .. } | r2ssa::SSAOp::PtrSub { base, .. } => {
            prepared_var_base_param_slot(prepared, base, param_slots, depth + 1)
        }
        _ => None,
    }
}

fn prepared_var_base_param_slot(
    prepared: &r2ssa::SsaArtifact,
    var: &r2ssa::SSAVar,
    param_slots: &ParamSlotResolver,
    depth: usize,
) -> Option<usize> {
    let value = prepared.graph().value_id_for_var(var)?;
    prepared_address_base_param_slot(prepared, value, param_slots, depth)
}

fn prepared_add_param_slot(
    prepared: &r2ssa::SsaArtifact,
    a: &r2ssa::SSAVar,
    b: &r2ssa::SSAVar,
    param_slots: &ParamSlotResolver,
    depth: usize,
) -> Option<usize> {
    match (const_var_i64(a), const_var_i64(b)) {
        (None, Some(_)) => prepared_var_base_param_slot(prepared, a, param_slots, depth),
        (Some(_), None) => prepared_var_base_param_slot(prepared, b, param_slots, depth),
        _ => None,
    }
}

fn prepared_sub_param_slot(
    prepared: &r2ssa::SsaArtifact,
    a: &r2ssa::SSAVar,
    b: &r2ssa::SSAVar,
    param_slots: &ParamSlotResolver,
    depth: usize,
) -> Option<usize> {
    match (const_var_i64(a), const_var_i64(b)) {
        (None, Some(_)) => prepared_var_base_param_slot(prepared, a, param_slots, depth),
        _ => None,
    }
}

fn const_var_i64(var: &r2ssa::SSAVar) -> Option<i64> {
    let raw = r2ssa::parse_const_value(&var.name)?;
    let bits = var.size.saturating_mul(8);
    if bits == 0 || bits >= 64 {
        return Some(raw as i64);
    }
    let sign_bit = 1u64.checked_shl(bits - 1)?;
    let mask = 1u64.checked_shl(bits)?.wrapping_sub(1);
    let truncated = raw & mask;
    if truncated & sign_bit == 0 {
        Some(truncated as i64)
    } else {
        Some((truncated | !mask) as i64)
    }
}

fn prepared_render_facts(prepared: &r2ssa::SsaArtifact) -> FunctionRenderFacts {
    let certificates = prepared.certificates();
    let expressions = certificates
        .expressions
        .iter()
        .map(|(value, cert)| {
            (
                *value,
                ExpressionRenderFact {
                    value: cert.value,
                    defining_inst: cert.defining_inst,
                    width: cert.width,
                    renderable: cert.renderable,
                },
            )
        })
        .collect();
    let memory_accesses = certificates
        .memory_accesses
        .iter()
        .map(|(access, cert)| {
            (
                *access,
                MemoryAccessRenderFact {
                    access: cert.access,
                    block_addr: cert.block_addr,
                    op_index: cert.op_index,
                    object: cert.object,
                    address: cert.address,
                    value: cert.value,
                    is_write: cert.is_write,
                    width: cert.width,
                },
            )
        })
        .collect();
    let memory_accesses_by_op = certificates.memory_accesses_by_op.clone();
    let returns_by_op = certificates
        .returns
        .iter()
        .map(|cert| {
            (
                (cert.block_addr, cert.op_index),
                ReturnValueRenderFact {
                    block_addr: cert.block_addr,
                    op_index: cert.op_index,
                    value: cert.value,
                    width: cert.width,
                },
            )
        })
        .collect();
    let mut stack_slot_offsets: BTreeMap<_, _> = certificates
        .stack_slots
        .iter()
        .map(|(object, cert)| (*object, cert.offset))
        .collect();
    for cert in certificates.memory_accesses.values() {
        stack_slot_offsets.entry(cert.object).or_insert_with(|| {
            prepared
                .objects()
                .object(cert.object)
                .and_then(|object| match &object.kind {
                    r2ssa::ObjectKind::StackSlot { offset, .. }
                    | r2ssa::ObjectKind::FrameObject { offset, .. } => Some(offset),
                    _ => None,
                })
                .copied()
                .unwrap_or(0)
        });
    }
    stack_slot_offsets.retain(|object, _| {
        prepared.objects().object(*object).is_some_and(|object| {
            matches!(
                &object.kind,
                r2ssa::ObjectKind::StackSlot { .. } | r2ssa::ObjectKind::FrameObject { .. }
            )
        })
    });
    FunctionRenderFacts {
        expressions,
        string_literals_by_value: BTreeMap::new(),
        memory_accesses,
        memory_accesses_by_op,
        member_accesses_by_op: BTreeMap::new(),
        array_accesses_by_op: BTreeMap::new(),
        returns_by_op,
        stack_slot_offsets,
    }
}

fn prepared_control_facts(prepared: &r2ssa::SsaArtifact) -> FunctionControlFacts {
    let predicates = prepared.predicates();
    let certificates = prepared.certificates();
    let branch_predicates = predicates
        .predicates
        .values()
        .map(|predicate| {
            (
                predicate.block_addr,
                BranchPredicateFact {
                    id: predicate.id,
                    block_addr: predicate.block_addr,
                    condition: predicate.condition,
                    comparison: predicate.comparison.as_ref().map(|comparison| {
                        PredicateComparisonFact {
                            kind: comparison.kind,
                            lhs: comparison.lhs,
                            rhs: comparison.rhs,
                        }
                    }),
                    true_target: predicate.true_target,
                    false_target: predicate.false_target,
                },
            )
        })
        .collect();
    let block_assumptions = predicates
        .block_assumptions
        .iter()
        .map(|(block_addr, assumptions)| {
            (
                *block_addr,
                assumptions
                    .iter()
                    .map(|assumption| ControlBlockAssumptionFact {
                        predecessor: assumption.predecessor,
                        predicate: assumption.predicate,
                        truth: assumption.truth,
                    })
                    .collect(),
            )
        })
        .collect();
    let loops = certificates
        .loops
        .iter()
        .map(|(loop_id, cert)| {
            (
                *loop_id,
                LoopStructureFact {
                    loop_id: *loop_id,
                    proof_node: cert.proof_node.to_string(),
                    header: cert.header,
                    condition: cert.condition,
                    condition_value: cert.condition.and_then(|id| {
                        predicates
                            .predicates
                            .get(&id)
                            .map(|predicate| predicate.condition)
                    }),
                    body: sorted_u64s(&cert.body),
                    latches: sorted_u64s(&cert.latches),
                    exits: sorted_u64s(&cert.exits),
                },
            )
        })
        .collect();
    let switches = predicates
        .switches
        .iter()
        .map(|(block_addr, switch)| {
            (
                *block_addr,
                SwitchSelectorFact {
                    proof_node: r2ssa::ProofNodeId::switch_certificate(*block_addr).to_string(),
                    block_addr: switch.block_addr,
                    selector: switch.selector,
                    cases: switch.cases.clone(),
                    default: switch.default,
                },
            )
        })
        .collect();
    FunctionControlFacts {
        branch_predicates,
        block_assumptions,
        loops,
        switches,
    }
}

fn sorted_u64s(values: &[u64]) -> Vec<u64> {
    let mut values = values.to_vec();
    values.sort_unstable();
    values
}

fn summary_rollup(set: Option<&r2ssa::InterprocSummarySet>) -> Option<SummaryEffectRollup> {
    let set = set?;
    let root_summary = set.root.and_then(|root| set.summaries.get(&root));
    let out_param_facts = root_summary
        .map(summary_out_param_facts)
        .unwrap_or_default();

    let mut pointer_param_indices = root_summary
        .map(|summary| {
            let mut indices = summary
                .arg_effects
                .iter()
                .filter_map(|(idx, effect)| {
                    (effect.read || effect.write || effect.escape || effect.free).then_some(*idx)
                })
                .collect::<Vec<_>>();
            for effect in &summary.memory_effects {
                if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.location.region {
                    indices.push(index);
                }
            }
            push_structured_summary_pointer_indices(summary, &mut indices);
            indices
        })
        .unwrap_or_default();
    pointer_param_indices.sort_unstable();
    pointer_param_indices.dedup();

    Some(SummaryEffectRollup {
        root_name: root_summary.and_then(|summary| summary.name.clone()),
        root_return_relation: root_summary.map(|summary| summary.return_relation.clone()),
        out_param_facts,
        pointer_param_indices,
        transfer_count: root_summary.map_or(0, |summary| summary.transfer_effects.len()),
        allocation_count: root_summary.map_or(0, |summary| summary.allocation_effects.len()),
        lifetime_count: root_summary.map_or(0, |summary| summary.lifetime_effects.len()),
        sync_count: root_summary.map_or(0, |summary| summary.sync_effects.len()),
        atomic_count: root_summary.map_or(0, |summary| summary.atomic_effects.len()),
        helper_summary_count: set
            .summaries
            .len()
            .saturating_sub(usize::from(set.root.is_some())),
        has_unknown_calls: root_summary.is_some_and(|summary| summary.has_unknown_calls),
        touches_unknown_memory: root_summary.is_some_and(|summary| summary.touches_unknown_memory),
    })
}

fn helper_views(set: Option<&r2ssa::InterprocSummarySet>) -> Vec<SummaryHelperView> {
    let Some(set) = set else {
        return Vec::new();
    };
    let mut helpers = set
        .summaries
        .iter()
        .filter(|(id, _)| Some(**id) != set.root)
        .map(|(id, summary)| {
            let out_param_facts = summary_out_param_facts(summary);

            let mut pointer_param_indices = summary
                .arg_effects
                .iter()
                .filter_map(|(idx, effect)| {
                    (effect.read || effect.write || effect.escape || effect.free).then_some(*idx)
                })
                .collect::<Vec<_>>();
            for effect in &summary.memory_effects {
                if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.location.region {
                    pointer_param_indices.push(index);
                }
            }
            push_structured_summary_pointer_indices(summary, &mut pointer_param_indices);
            pointer_param_indices.sort_unstable();
            pointer_param_indices.dedup();

            SummaryHelperView {
                function_id: id.0,
                name: summary.name.clone(),
                arg_count_hint: summary.arg_count_hint,
                return_relation: summary.return_relation.clone(),
                out_param_facts,
                pointer_param_indices,
                transfer_effects: summary.transfer_effects.clone(),
                allocation_effects: summary.allocation_effects.clone(),
                lifetime_effects: summary.lifetime_effects.clone(),
                sync_effects: summary.sync_effects.clone(),
                atomic_effects: summary.atomic_effects.clone(),
                has_unknown_calls: summary.has_unknown_calls,
                touches_unknown_memory: summary.touches_unknown_memory,
            }
        })
        .collect::<Vec<_>>();
    helpers.sort_by(|left, right| {
        left.name
            .cmp(&right.name)
            .then(left.function_id.cmp(&right.function_id))
    });
    helpers
}

fn summary_out_param_facts(summary: &r2ssa::FunctionSemanticSummary) -> Vec<SummaryOutParamFact> {
    let mut facts = summary
        .arg_effects
        .iter()
        .enumerate()
        .filter(|(_, (_, effect))| effect.write)
        .map(|(effect_index, (idx, _))| SummaryOutParamFact {
            param_index: *idx,
            evidence: OutParamCertificateEvidence::InterprocArgWrite,
            source: OutParamCertificateSource::InterprocSummaryEffect {
                function_id: summary.id.0,
                evidence: OutParamCertificateEvidence::InterprocArgWrite,
                param_index: *idx,
                effect_index,
            },
        })
        .collect::<Vec<_>>();
    for (effect_index, effect) in summary.memory_effects.iter().enumerate() {
        if effect.kind == r2ssa::SummaryMemoryEffectKind::Write
            && let r2ssa::SummaryMemoryRegion::Arg { index } = effect.location.region
        {
            facts.push(SummaryOutParamFact {
                param_index: index,
                evidence: OutParamCertificateEvidence::InterprocMemoryWrite,
                source: OutParamCertificateSource::InterprocSummaryEffect {
                    function_id: summary.id.0,
                    evidence: OutParamCertificateEvidence::InterprocMemoryWrite,
                    param_index: index,
                    effect_index,
                },
            });
        }
    }
    for (effect_index, effect) in summary.transfer_effects.iter().enumerate() {
        if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.dst.region {
            facts.push(SummaryOutParamFact {
                param_index: index,
                evidence: OutParamCertificateEvidence::InterprocTransferDst,
                source: OutParamCertificateSource::InterprocSummaryEffect {
                    function_id: summary.id.0,
                    evidence: OutParamCertificateEvidence::InterprocTransferDst,
                    param_index: index,
                    effect_index,
                },
            });
        }
    }
    facts.sort();
    facts.dedup();
    facts
}

fn out_param_indices_from_facts(facts: &[SummaryOutParamFact]) -> Vec<usize> {
    let mut indices = facts
        .iter()
        .map(|fact| fact.param_index)
        .collect::<Vec<_>>();
    indices.sort_unstable();
    indices.dedup();
    indices
}

fn push_structured_summary_pointer_indices(
    summary: &r2ssa::FunctionSemanticSummary,
    indices: &mut Vec<usize>,
) {
    for effect in &summary.transfer_effects {
        if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.dst.region {
            indices.push(index);
        }
        if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.src.region {
            indices.push(index);
        }
    }
    for effect in &summary.lifetime_effects {
        indices.push(effect.arg);
    }
    for effect in &summary.sync_effects {
        indices.push(effect.arg);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FunctionParamSpec;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use std::collections::{BTreeMap, HashMap};

    #[test]
    fn function_facts_owns_input_quality_evidence() {
        let complete = FunctionInputQualityFacts {
            expected_blocks: 2,
            lifted_blocks: 2,
            actual_lifted_blocks: 2,
            read_failures: 0,
            invalid_blocks: 0,
            null_lift_failures: 0,
            truncated_blocks: 0,
            refusal_reason: None,
        };
        assert!(complete.is_complete());

        let refused = FunctionInputQualityFacts {
            expected_blocks: 2,
            lifted_blocks: 1,
            actual_lifted_blocks: 1,
            read_failures: 1,
            invalid_blocks: 0,
            null_lift_failures: 0,
            truncated_blocks: 0,
            refusal_reason: Some("incomplete lifted function input".to_string()),
        };
        assert!(!refused.is_complete());

        let mismatch = FunctionInputQualityFacts {
            expected_blocks: 2,
            lifted_blocks: 2,
            actual_lifted_blocks: 1,
            read_failures: 0,
            invalid_blocks: 0,
            null_lift_failures: 0,
            truncated_blocks: 0,
            refusal_reason: Some("inconsistent lifted function input".to_string()),
        };
        assert!(!mismatch.is_complete());

        let mut facts = FunctionFacts::default().with_input_quality(refused.clone());
        assert_eq!(facts.input_quality(), Some(&refused));
        assert!(
            !facts.input_quality().expect("quality fact").is_complete(),
            "incomplete lift quality must travel as refusal evidence"
        );

        facts.set_input_quality(Some(complete.clone()));
        assert_eq!(facts.input_quality(), Some(&complete));
        assert!(facts.input_quality().expect("quality fact").is_complete());

        facts.set_input_quality(Some(mismatch.clone()));
        assert_eq!(facts.input_quality(), Some(&mismatch));
        assert!(!facts.input_quality().expect("quality fact").is_complete());

        facts.set_input_quality(None);
        assert_eq!(facts.input_quality(), None);
    }

    #[test]
    fn function_facts_owns_canonical_callee_resolution() {
        let callsite = crate::CallsiteKey {
            block_addr: 0x401000,
            op_index: 3,
        };
        let function_names = HashMap::from([(0x402000, "sym.helper".to_string())]);
        let symbols = HashMap::new();
        let known_function_signatures = HashMap::new();
        let callee_facts = BTreeMap::new();
        let ctx = crate::CalleeIdentityContext {
            function_names: &function_names,
            symbols: &symbols,
            callee_facts: &callee_facts,
            known_function_signatures: &known_function_signatures,
        };
        let resolution =
            CalleeResolutionFacts::from_direct_call_targets([(callsite, 0x402000)], &ctx);

        let facts = FunctionFacts::default().with_callee_resolution(resolution);

        assert!(
            facts
                .callee_resolution()
                .and_then(|resolution| resolution.identity_for_callsite(callsite))
                .is_some(),
            "callsite identity must travel through FunctionFacts, not a render side channel"
        );
    }

    #[test]
    fn function_facts_owns_canonical_callsite_arguments() {
        let callsite = crate::CallsiteKey {
            block_addr: 0x401000,
            op_index: 7,
        };
        let value = r2ssa::ValueId(11);
        let callsites = FunctionCallsiteFacts {
            by_callsite: BTreeMap::from([(
                callsite,
                CallsiteArgumentFacts {
                    callsite,
                    call_site_id: r2ssa::CallSiteId(2),
                    at: r2ssa::InstId(5),
                    target: r2ssa::ValueId(10),
                    direct_target: Some(0x402000),
                    argument_values: vec![CallArgumentValueFact { index: 0, value }],
                    register_argument_locations: vec![RegisterCallArgumentLocationFact {
                        index: 0,
                        value,
                        name: "rdi".to_string(),
                        source_inst: Some(r2ssa::InstId(4)),
                    }],
                    stack_argument_locations: Vec::new(),
                },
            )]),
        };

        let facts = FunctionFacts::default().with_callsites(callsites);

        assert_eq!(
            facts
                .callsites()
                .and_then(|callsites| callsites.arguments_for_site(callsite))
                .and_then(|args| args.argument_value(0)),
            Some(value),
            "callsite argument proof must travel through FunctionFacts, not r2dec local inference"
        );
        assert_eq!(
            facts
                .callsites()
                .and_then(|callsites| callsites.arguments_for_site(callsite))
                .and_then(|args| args.register_argument_locations.first())
                .map(|location| (location.index, location.value, location.name.as_str())),
            Some((0, value, "rdi")),
            "register argument location proof must travel through FunctionFacts"
        );
    }

    #[test]
    fn function_facts_owns_canonical_call_render_disposition() {
        let callsite = crate::CallsiteKey {
            block_addr: 0x401000,
            op_index: 7,
        };
        let target = r2ssa::ValueId(10);
        let arg = r2ssa::ValueId(11);
        let render = FunctionCallRenderFacts {
            by_callsite: BTreeMap::from([(
                callsite,
                CallsiteRenderFact {
                    callsite,
                    target: Some(target),
                    disposition: CallsiteRenderDisposition::AssignedResult,
                    proof_values: vec![arg],
                    residual_reason: None,
                },
            )]),
        };

        let facts = FunctionFacts::default().with_call_render(render);

        let fact = facts
            .call_render()
            .and_then(|render| render.fact_for_site(callsite))
            .expect("call render fact must travel through FunctionFacts");
        assert_eq!(fact.target, Some(target));
        assert_eq!(fact.disposition, CallsiteRenderDisposition::AssignedResult);
        assert_eq!(fact.proof_values, vec![arg]);
    }

    #[test]
    fn callsite_facts_own_canonical_argument_vector() {
        let callsite = crate::CallsiteKey {
            block_addr: 0x401000,
            op_index: 7,
        };
        let register_value = r2ssa::ValueId(11);
        let stack_value = r2ssa::ValueId(12);
        let duplicate_stack_value = r2ssa::ValueId(99);
        let args = CallsiteArgumentFacts {
            callsite,
            call_site_id: r2ssa::CallSiteId(2),
            at: r2ssa::InstId(5),
            target: r2ssa::ValueId(10),
            direct_target: Some(0x402000),
            argument_values: vec![CallArgumentValueFact {
                index: 0,
                value: register_value,
            }],
            register_argument_locations: vec![RegisterCallArgumentLocationFact {
                index: 0,
                value: register_value,
                name: "rdi".to_string(),
                source_inst: Some(r2ssa::InstId(4)),
            }],
            stack_argument_locations: vec![
                StackCallArgumentLocationFact {
                    index: 0,
                    value: duplicate_stack_value,
                    object: r2ssa::ObjectId(1),
                    offset: 0x20,
                    memory_access: r2ssa::StructuredAccessId {
                        inst: r2ssa::InstId(3),
                        ordinal: 0,
                    },
                    source_inst: Some(r2ssa::InstId(3)),
                },
                StackCallArgumentLocationFact {
                    index: 1,
                    value: stack_value,
                    object: r2ssa::ObjectId(2),
                    offset: 0x28,
                    memory_access: r2ssa::StructuredAccessId {
                        inst: r2ssa::InstId(4),
                        ordinal: 0,
                    },
                    source_inst: Some(r2ssa::InstId(4)),
                },
            ],
        };

        assert_eq!(
            args.canonical_argument_values(),
            vec![register_value, stack_value],
            "canonical callsite argument ordering and stack fallback must be owned by r2types"
        );
    }

    #[test]
    fn function_facts_owns_canonical_call_results() {
        let callsite = crate::CallsiteKey {
            block_addr: 0x401000,
            op_index: 7,
        };
        let value = r2ssa::ValueId(21);
        let owner = r2ssa::ValueOwner::StackSlot {
            object: r2ssa::ObjectId(3),
            offset: -8,
        };
        let call_results = FunctionCallResultFacts {
            by_value: BTreeMap::from([(
                value,
                CallResultFact {
                    callsite,
                    call_site_id: r2ssa::CallSiteId(2),
                    at: r2ssa::InstId(8),
                    value,
                    width: 8,
                    carrier: r2ssa::ReturnCarrier::Register {
                        name: "rax".to_string(),
                    },
                    owner: Some(owner.clone()),
                },
            )]),
            by_callsite: BTreeMap::from([(callsite, vec![value])]),
        };

        let facts = FunctionFacts::default().with_call_results(call_results);

        assert_eq!(
            facts
                .call_results()
                .and_then(|results| results.result_for_value(value))
                .and_then(|result| result.owner.as_ref()),
            Some(&owner),
            "call-result ownership proof must travel through FunctionFacts, not r2dec local inference"
        );
        assert_eq!(
            facts
                .call_results()
                .map(|results| results.results_for_site(callsite).count()),
            Some(1),
            "call-result site index must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .call_results()
                .and_then(|results| results.owner_for_site(callsite)),
            Some(&owner),
            "call-result owner lookup must be available by callsite"
        );
    }

    #[test]
    fn prepared_decompile_evidence_preserves_existing_function_facts() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x402000, 8),
        });
        let prepared = r2ssa::SsaArtifact::for_decompile(&[block], Some(&x86_stack_home_arch()))
            .expect("prepared");
        let callsite = CallsiteKey {
            block_addr: 0x401000,
            op_index: 0,
        };
        let sentinel_value = r2ssa::ValueId(0xfeed);
        let sentinel_callsite = CallsiteArgumentFacts {
            callsite,
            call_site_id: r2ssa::CallSiteId(0xbeef),
            at: r2ssa::InstId(0xbeef),
            target: sentinel_value,
            direct_target: Some(0x5555),
            argument_values: vec![CallArgumentValueFact {
                index: 0,
                value: sentinel_value,
            }],
            register_argument_locations: Vec::new(),
            stack_argument_locations: Vec::new(),
        };
        let sentinel_render = CallsiteRenderFact {
            callsite,
            target: Some(sentinel_value),
            disposition: CallsiteRenderDisposition::Residualized,
            proof_values: vec![sentinel_value],
            residual_reason: Some("upstream refusal".to_string()),
        };
        let string_value = r2ssa::ValueId(0xcafe);
        let member_op = (0x501000, 3, false);
        let member_access = MemberAccessRenderFact {
            access: r2ssa::StructuredAccessId {
                inst: r2ssa::InstId(7),
                ordinal: 0,
            },
            block_addr: member_op.0,
            op_index: member_op.1,
            object: r2ssa::ObjectId(9),
            is_write: false,
            field_offset: 8,
            field_name: "len".to_string(),
            access_width: 32,
        };
        let existing_render = FunctionRenderFacts {
            string_literals_by_value: BTreeMap::from([(
                string_value,
                StringLiteralRenderFact {
                    value: string_value,
                    address: 0x600000,
                    text: "existing".to_string(),
                    source: StringLiteralRenderSource::TypedFunctionFacts,
                },
            )]),
            member_accesses_by_op: BTreeMap::from([(member_op, vec![member_access.clone()])]),
            ..FunctionRenderFacts::default()
        };
        let mut facts = FunctionFacts::default()
            .with_callsites(FunctionCallsiteFacts {
                by_callsite: BTreeMap::from([(callsite, sentinel_callsite.clone())]),
            })
            .with_call_render(FunctionCallRenderFacts {
                by_callsite: BTreeMap::from([(callsite, sentinel_render.clone())]),
            })
            .with_render(existing_render);

        facts.attach_prepared_decompile_evidence(&prepared);

        assert_eq!(
            facts
                .callsites()
                .and_then(|callsites| callsites.arguments_for_site(callsite)),
            Some(&sentinel_callsite),
            "prepared callsite evidence must not overwrite existing FunctionFacts callsite proof"
        );
        assert_eq!(
            facts
                .call_render()
                .and_then(|render| render.fact_for_site(callsite)),
            Some(&sentinel_render),
            "prepared call-render evidence must not overwrite existing FunctionFacts render disposition"
        );
        assert_eq!(
            facts
                .render()
                .and_then(|render| render.string_literal_for_value(string_value))
                .map(|literal| literal.text.as_str()),
            Some("existing"),
            "prepared render facts must not erase existing string literal render evidence"
        );
        assert_eq!(
            facts
                .render()
                .and_then(|render| render.member_accesses_by_op.get(&member_op))
                .and_then(|members| members.first()),
            Some(&member_access),
            "prepared render facts must not erase existing member-access evidence"
        );
        assert!(
            facts
                .callee_resolution()
                .and_then(|resolution| resolution.identity_for_callsite(callsite))
                .is_some(),
            "prepared evidence should still fill missing FunctionFacts groups"
        );
    }

    #[test]
    fn field_certificates_populate_direct_member_render_facts() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        let prepared = r2ssa::SsaArtifact::for_decompile(&[block], Some(&x86_stack_home_arch()))
            .expect("prepared");
        let type_facts = FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 0,
                field_offset: 8,
                field_name: "hash".to_string(),
                field_type: Some("uint64_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(),
        );

        assert!(
            facts.render().is_some_and(|render| render
                .member_access_for_op(0x401000, 1, false, "hash", 8, Some(8))
                .is_some()),
            "field certificate plus prepared memory address proof must authorize direct member rendering"
        );
    }

    #[test]
    fn field_certificates_do_not_populate_member_render_facts_for_wrong_width() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        let prepared = r2ssa::SsaArtifact::for_decompile(&[block], Some(&x86_stack_home_arch()))
            .expect("prepared");
        let type_facts = FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 0,
                field_offset: 8,
                field_name: "small".to_string(),
                field_type: Some("uint32_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(),
        );

        assert!(
            facts.render().is_none_or(|render| render
                .member_access_for_op(0x401000, 1, false, "small", 8, Some(8))
                .is_none()),
            "wrong-width field certificate must not authorize member rendering"
        );
    }

    #[test]
    fn field_certificates_do_not_populate_member_render_facts_for_wrong_param_slot() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x18, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        let prepared = r2ssa::SsaArtifact::for_decompile(&[block], Some(&x86_stack_home_arch()))
            .expect("prepared");
        let type_facts = FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 0,
                field_offset: 8,
                field_name: "hash".to_string(),
                field_type: Some("uint64_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(),
        );

        assert!(
            facts.render().is_none_or(|render| render
                .member_access_for_op(0x401000, 1, false, "hash", 8, Some(8))
                .is_none()),
            "a field certificate for one parameter slot must not authorize the same offset on another parameter"
        );

        let matching_type_facts = FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 1,
                field_offset: 8,
                field_name: "hash".to_string(),
                field_type: Some("uint64_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut matching_facts = FunctionFacts::new(matching_type_facts, None);

        matching_facts.attach_prepared_decompile_evidence(&prepared);
        matching_facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(),
        );

        assert!(
            matching_facts.render().is_some_and(|render| render
                .member_access_for_op(0x401000, 1, false, "hash", 8, Some(8))
                .is_some()),
            "the same memory proof should authorize the certificate for the matching parameter slot"
        );
    }

    fn x86_stack_home_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("rax", 0x00, 8));
        arch.add_register(RegisterDef::sub("eax", 0x00, 4, "rax"));
        arch.add_register(RegisterDef::new("rdi", 0x10, 8));
        arch.add_register(RegisterDef::new("rsi", 0x18, 8));
        arch.add_register(RegisterDef::new("rbp", 0x20, 8));
        arch
    }

    fn x86_stack_home_param_slots() -> ParamSlotResolver {
        ParamSlotResolver::from_arch_name(Some("x86-64"))
    }

    fn member_load_prepared_for_register(
        arch: &ArchSpec,
        register_offset: u64,
    ) -> r2ssa::SsaArtifact {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(register_offset, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        r2ssa::SsaArtifact::for_decompile(&[block], Some(arch)).expect("prepared")
    }

    fn field_certificate_type_facts(slot: usize, offset: u64) -> FunctionTypeFacts {
        FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot,
                field_offset: offset,
                field_name: "hash".to_string(),
                field_type: Some("uint64_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        }
    }

    #[test]
    fn param_slot_resolver_maps_explicit_windows_x64_register_order() {
        let resolver = ParamSlotResolver::from_arg_regs(["rcx", "rdx"]);

        assert_eq!(resolver.slot_for_register_name("rcx"), Some(0));
        assert_eq!(resolver.slot_for_register_name("ecx"), Some(0));
        assert_eq!(resolver.slot_for_register_name("rdx"), Some(1));
        assert_eq!(resolver.slot_for_register_name("edx"), Some(1));
        assert_eq!(resolver.slot_for_register_name("rdi"), None);
    }

    #[test]
    fn param_slot_resolver_maps_aarch64_aliases_from_abi_evidence() {
        let resolver = ParamSlotResolver::from_arch_name(Some("aarch64"));

        assert_eq!(resolver.slot_for_register_name("x0"), Some(0));
        assert_eq!(resolver.slot_for_register_name("w0"), Some(0));
        assert_eq!(resolver.slot_for_register_name("x1"), Some(1));
        assert_eq!(resolver.slot_for_register_name("w1"), Some(1));
    }

    #[test]
    fn field_certificates_fail_closed_without_param_slot_resolver() {
        let prepared = member_load_prepared_for_register(&x86_stack_home_arch(), 0x10);
        let mut facts = FunctionFacts::new(field_certificate_type_facts(0, 8), None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &ParamSlotResolver::new(),
        );

        assert!(
            facts.render().is_none_or(|render| render
                .member_access_for_op(0x401000, 1, false, "hash", 8, Some(8))
                .is_none()),
            "missing ABI slot evidence must not guess rdi as parameter slot 0"
        );
    }

    #[test]
    fn field_certificates_use_explicit_windows_x64_param_slots() {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("rax", 0x00, 8));
        arch.add_register(RegisterDef::new("rcx", 0x10, 8));
        arch.add_register(RegisterDef::new("rdx", 0x18, 8));
        let param_slots = ParamSlotResolver::from_arg_regs(["rcx", "rdx"]);

        let rcx_prepared = member_load_prepared_for_register(&arch, 0x10);
        let mut rcx_facts = FunctionFacts::new(field_certificate_type_facts(0, 8), None);
        rcx_facts.attach_prepared_decompile_evidence(&rcx_prepared);
        rcx_facts.populate_member_access_render_facts_from_field_certificates(
            &rcx_prepared,
            &param_slots,
        );
        assert!(
            rcx_facts.render().is_some_and(|render| render
                .member_access_for_op(0x401000, 1, false, "hash", 8, Some(8))
                .is_some()),
            "explicit Windows x64 resolver must map rcx to slot 0"
        );

        let rdx_prepared = member_load_prepared_for_register(&arch, 0x18);
        let mut wrong_slot_facts = FunctionFacts::new(field_certificate_type_facts(0, 8), None);
        wrong_slot_facts.attach_prepared_decompile_evidence(&rdx_prepared);
        wrong_slot_facts.populate_member_access_render_facts_from_field_certificates(
            &rdx_prepared,
            &param_slots,
        );
        assert!(
            wrong_slot_facts.render().is_none_or(|render| render
                .member_access_for_op(0x401000, 1, false, "hash", 8, Some(8))
                .is_none()),
            "slot 0 certificate must not authorize rdx when resolver maps rdx to slot 1"
        );

        let mut matching_slot_facts = FunctionFacts::new(field_certificate_type_facts(1, 8), None);
        matching_slot_facts.attach_prepared_decompile_evidence(&rdx_prepared);
        matching_slot_facts.populate_member_access_render_facts_from_field_certificates(
            &rdx_prepared,
            &param_slots,
        );
        assert!(
            matching_slot_facts.render().is_some_and(|render| render
                .member_access_for_op(0x401000, 1, false, "hash", 8, Some(8))
                .is_some()),
            "explicit Windows x64 resolver must map rdx to slot 1"
        );
    }

    fn stack_home_field_load_prepared(with_store: bool) -> r2ssa::SsaArtifact {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x20, 8),
            b: Varnode::constant(0xffff_ffff_ffff_fff8, 8),
        });
        if with_store {
            block.push(R2ILOp::Copy {
                dst: Varnode::unique(0x104, 8),
                src: Varnode::register(0x10, 8),
            });
            block.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::unique(0x100, 8),
                val: Varnode::unique(0x104, 8),
            });
        }
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x108, 8),
            a: Varnode::register(0x20, 8),
            b: Varnode::constant(0xffff_ffff_ffff_fff8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x110, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x108, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x118, 8),
            a: Varnode::unique(0x110, 8),
            b: Varnode::constant(4, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x118, 8),
        });
        r2ssa::SsaArtifact::for_decompile(&[block], Some(&x86_stack_home_arch())).expect("prepared")
    }

    #[test]
    fn field_certificates_populate_stack_home_member_render_facts() {
        let prepared = stack_home_field_load_prepared(true);
        let type_facts = FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 0,
                field_offset: 4,
                field_name: "hash".to_string(),
                field_type: Some("uint32_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(),
        );

        assert!(
            facts.render().is_some_and(|render| render
                .member_access_for_op(0x401000, 6, false, "hash", 4, Some(4))
                .is_some()),
            "field certificate plus prepared stack-reload proof must authorize O0 stack-home member rendering"
        );
    }

    #[test]
    fn field_certificates_do_not_populate_stack_home_member_without_reload_proof() {
        let prepared = stack_home_field_load_prepared(false);
        let type_facts = FunctionTypeFacts {
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 0,
                field_offset: 4,
                field_name: "hash".to_string(),
                field_type: Some("uint32_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(),
        );

        assert!(
            facts.render().is_none_or(|render| render
                .member_access_for_op(0x401000, 4, false, "hash", 4, Some(4))
                .is_none()),
            "field certificate must not authorize a member render through an unproven stack load"
        );
    }

    #[test]
    fn scalar_array_candidates_populate_indexed_member_render_facts() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 4),
            space: SpaceId::Ram,
            addr: Varnode::register(0x10, 8),
        });
        let prepared = r2ssa::SsaArtifact::for_decompile(&[block], Some(&x86_stack_home_arch()))
            .expect("prepared");
        let type_facts = FunctionTypeFacts {
            array_index_certificates: vec![crate::facts::ArrayIndexCertificate {
                slot: 0,
                base: Some(crate::facts::ArrayIndexBase::Param { index: 0 }),
                field_offset: 4,
                element_stride: 16,
            }],
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot: 0,
                field_offset: 4,
                field_name: "score".to_string(),
                field_type: Some("int32_t".to_string()),
            }],
            scalar_array_render_candidates: vec![crate::facts::ScalarArrayRenderCandidate {
                slot: 0,
                block_addr: 0x401000,
                op_index: 0,
                is_write: false,
                field_offset: 4,
                element_stride: 16,
                access_width: 4,
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.attach_prepared_decompile_evidence(&prepared);
        facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(),
        );
        facts.populate_array_access_render_facts_from_scalar_candidates(
            &prepared,
            &x86_stack_home_param_slots(),
        );

        let render = facts.render().expect("render facts");
        assert!(
            render
                .member_access_for_op(0x401000, 0, false, "score", 4, Some(4))
                .is_some(),
            "scalar array candidate plus field certificate must authorize indexed member rendering"
        );
        assert!(
            render
                .array_access_for_op(0x401000, 0, false, 4, 16, Some(4))
                .is_some(),
            "scalar array candidate must still authorize array rendering"
        );
    }

    #[test]
    fn scalar_array_member_candidate_requires_matching_second_param_slot() {
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 4),
            space: SpaceId::Ram,
            addr: Varnode::register(0x18, 8),
        });
        let prepared = r2ssa::SsaArtifact::for_decompile(&[block], Some(&x86_stack_home_arch()))
            .expect("prepared");
        let type_facts_for_slot = |slot| FunctionTypeFacts {
            array_index_certificates: vec![crate::facts::ArrayIndexCertificate {
                slot,
                base: Some(crate::facts::ArrayIndexBase::Param { index: slot }),
                field_offset: 4,
                element_stride: 16,
            }],
            field_access_certificates: vec![crate::facts::FieldAccessCertificate {
                slot,
                field_offset: 4,
                field_name: "score".to_string(),
                field_type: Some("int32_t".to_string()),
            }],
            scalar_array_render_candidates: vec![crate::facts::ScalarArrayRenderCandidate {
                slot,
                block_addr: 0x401000,
                op_index: 0,
                is_write: false,
                field_offset: 4,
                element_stride: 16,
                access_width: 4,
            }],
            ..FunctionTypeFacts::default()
        };

        let mut wrong_slot_facts = FunctionFacts::new(type_facts_for_slot(0), None);
        wrong_slot_facts.attach_prepared_decompile_evidence(&prepared);
        wrong_slot_facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(),
        );
        assert!(
            wrong_slot_facts.render().is_none_or(|render| render
                .member_access_for_op(0x401000, 0, false, "score", 4, Some(4))
                .is_none()),
            "scalar-array member candidate from rsi must not render with a slot 0 certificate"
        );

        let mut matching_slot_facts = FunctionFacts::new(type_facts_for_slot(1), None);
        matching_slot_facts.attach_prepared_decompile_evidence(&prepared);
        matching_slot_facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_stack_home_param_slots(),
        );
        assert!(
            matching_slot_facts.render().is_some_and(|render| render
                .member_access_for_op(0x401000, 0, false, "score", 4, Some(4))
                .is_some()),
            "scalar-array member candidate from rsi must render with a slot 1 certificate"
        );
    }

    #[test]
    fn function_facts_owns_canonical_control_facts() {
        let branch = BranchPredicateFact {
            id: r2ssa::PredicateId(0),
            block_addr: 0x401000,
            condition: r2ssa::ValueId(31),
            comparison: Some(PredicateComparisonFact {
                kind: r2ssa::CompareKind::Equal,
                lhs: r2ssa::ValueId(32),
                rhs: r2ssa::ValueId(33),
            }),
            true_target: 0x401010,
            false_target: 0x401004,
        };
        let switch = SwitchSelectorFact {
            proof_node: r2ssa::ProofNodeId::switch_certificate(0x402000).to_string(),
            block_addr: 0x402000,
            selector: Some(r2ssa::ValueId(41)),
            cases: vec![(0, 0x402010), (1, 0x402020)],
            default: Some(0x402030),
        };
        let loop_fact = LoopStructureFact {
            loop_id: r2ssa::LoopId(2),
            proof_node: r2ssa::ProofNodeId::loop_certificate(0x403000, r2ssa::LoopId(2))
                .to_string(),
            header: 0x403000,
            condition: Some(branch.id),
            condition_value: Some(branch.condition),
            body: vec![0x403000, 0x403010],
            latches: vec![0x403010],
            exits: vec![0x403020],
        };
        let control = FunctionControlFacts {
            branch_predicates: BTreeMap::from([(branch.block_addr, branch.clone())]),
            block_assumptions: BTreeMap::from([(
                branch.true_target,
                vec![ControlBlockAssumptionFact {
                    predecessor: branch.block_addr,
                    predicate: branch.id,
                    truth: true,
                }],
            )]),
            loops: BTreeMap::from([(loop_fact.loop_id, loop_fact.clone())]),
            switches: BTreeMap::from([(switch.block_addr, switch.clone())]),
        };

        let facts = FunctionFacts::default().with_control(control);

        assert_eq!(
            facts
                .control()
                .and_then(|control| control.branch_for_block(0x401000)),
            Some(&branch),
            "branch predicate proof must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .control()
                .map(|control| control.assumptions_for_block(0x401010).count()),
            Some(1),
            "block assumption proof must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .control()
                .map(|control| control.loops_for_header(0x403000).count()),
            Some(1),
            "loop structure proof must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .control()
                .and_then(|control| control.switch_for_block(0x402000)),
            Some(&switch),
            "switch selector proof must travel through FunctionFacts"
        );
    }

    #[test]
    fn function_facts_owns_canonical_render_facts() {
        let value = r2ssa::ValueId(51);
        let access = r2ssa::StructuredAccessId {
            inst: r2ssa::InstId(7),
            ordinal: 0,
        };
        let object = r2ssa::ObjectId(3);
        let render = FunctionRenderFacts {
            expressions: BTreeMap::from([(
                value,
                ExpressionRenderFact {
                    value,
                    defining_inst: Some(r2ssa::InstId(8)),
                    width: 8,
                    renderable: true,
                },
            )]),
            string_literals_by_value: BTreeMap::from([(
                value,
                StringLiteralRenderFact {
                    value,
                    address: 0x402000,
                    text: "value".to_string(),
                    source: StringLiteralRenderSource::TypedFunctionFacts,
                },
            )]),
            memory_accesses: BTreeMap::from([(
                access,
                MemoryAccessRenderFact {
                    access,
                    block_addr: 0x401000,
                    op_index: 4,
                    object,
                    address: r2ssa::ValueId(52),
                    value: Some(value),
                    is_write: true,
                    width: 8,
                },
            )]),
            memory_accesses_by_op: BTreeMap::from([((0x401000, 4, true), vec![access])]),
            member_accesses_by_op: BTreeMap::from([(
                (0x401000, 4, true),
                vec![MemberAccessRenderFact {
                    access,
                    block_addr: 0x401000,
                    op_index: 4,
                    object,
                    is_write: true,
                    field_offset: 0,
                    field_name: "value".to_string(),
                    access_width: 8,
                }],
            )]),
            array_accesses_by_op: BTreeMap::from([(
                (0x401000, 4, true),
                vec![ArrayAccessRenderFact {
                    access,
                    block_addr: 0x401000,
                    op_index: 4,
                    object,
                    is_write: true,
                    field_offset: 0,
                    element_stride: 8,
                    access_width: 8,
                }],
            )]),
            returns_by_op: BTreeMap::from([(
                (0x401010, 2),
                ReturnValueRenderFact {
                    block_addr: 0x401010,
                    op_index: 2,
                    value,
                    width: 8,
                },
            )]),
            stack_slot_offsets: BTreeMap::from([(object, -8)]),
        };

        let facts = FunctionFacts::default().with_render(render);

        assert!(
            facts
                .render()
                .is_some_and(|render| render.expression_is_renderable(value)),
            "expression renderability proof must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .render()
                .and_then(|render| render.string_literal_for_value(value))
                .map(|literal| (literal.address, literal.text.as_str())),
            Some((0x402000, "value")),
            "string literal render proof must travel through FunctionFacts"
        );
        assert!(
            facts.render().is_some_and(|render| render
                .member_access_for_op(0x401000, 4, true, "value", 0, Some(8))
                .is_some()),
            "member access render proof must travel through FunctionFacts"
        );
        assert!(
            facts.render().is_some_and(|render| render
                .array_access_for_op(0x401000, 4, true, 0, 8, Some(8))
                .is_some()),
            "array access render proof must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .render()
                .and_then(|render| render.memory_access_for_op(0x401000, 4, true))
                .map(|memory| (memory.access, memory.value, memory.width)),
            Some((access, Some(value), 8)),
            "memory access proof must travel through FunctionFacts"
        );
        assert_eq!(
            facts
                .render()
                .and_then(|render| render.return_for_op(0x401010, 2))
                .map(|ret| (ret.value, ret.width)),
            Some((value, 8)),
            "return value proof must travel through FunctionFacts"
        );
        assert!(
            facts
                .render()
                .is_some_and(|render| render.has_stack_slot_offset(-8)),
            "stack-slot offset proof must travel through FunctionFacts"
        );
    }

    #[test]
    fn function_facts_authorizes_stack_owner_render_by_object_type_and_name() {
        let object = r2ssa::ObjectId(11);
        let facts = FunctionFacts::new(
            FunctionTypeFacts {
                visible_bindings: vec![crate::VisibleBinding {
                    name: "local_buf".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                        bits: 8,
                        signedness: crate::Signedness::Unsigned,
                    }))),
                    kind: VisibleBindingKind::Local,
                    stack_slot: Some(StackSlotKey {
                        base: ExternalStackBase::FramePointer,
                        offset: 8,
                    }),
                    param_index: None,
                    source_reg: None,
                }],
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(FunctionRenderFacts {
            stack_slot_offsets: BTreeMap::from([(object, -8)]),
            ..FunctionRenderFacts::default()
        });

        let authorization = facts
            .authorized_stack_slot_owner_render(object, -8, "LOCAL_BUF")
            .expect("typed visible binding plus exact render object should authorize owner");
        assert_eq!(authorization.object, object);
        assert_eq!(authorization.offset, -8);
        assert_eq!(authorization.name, "LOCAL_BUF");
        assert!(
            facts
                .authorized_stack_slot_owner_render(r2ssa::ObjectId(12), -8, "local_buf")
                .is_none(),
            "a matching offset must not authorize the wrong SSA object"
        );
    }

    #[test]
    fn function_render_facts_require_exact_array_access_identity() {
        let access = r2ssa::StructuredAccessId {
            inst: r2ssa::InstId(7),
            ordinal: 0,
        };
        let other_access = r2ssa::StructuredAccessId {
            inst: r2ssa::InstId(8),
            ordinal: 0,
        };
        let object = r2ssa::ObjectId(3);
        let value = r2ssa::ValueId(51);
        let render = FunctionRenderFacts {
            memory_accesses: BTreeMap::from([(
                access,
                MemoryAccessRenderFact {
                    access,
                    block_addr: 0x401000,
                    op_index: 4,
                    object,
                    address: r2ssa::ValueId(52),
                    value: Some(value),
                    is_write: false,
                    width: 4,
                },
            )]),
            memory_accesses_by_op: BTreeMap::from([((0x401000, 4, false), vec![access])]),
            array_accesses_by_op: BTreeMap::from([(
                (0x401000, 4, false),
                vec![ArrayAccessRenderFact {
                    access,
                    block_addr: 0x401000,
                    op_index: 4,
                    object,
                    is_write: false,
                    field_offset: 0,
                    element_stride: 4,
                    access_width: 4,
                }],
            )]),
            ..FunctionRenderFacts::default()
        };

        assert!(
            render
                .array_access_for_op(0x401000, 4, false, 0, 4, Some(4))
                .is_some(),
            "exact op/access/object/direction/width/stride identity should authorize array rendering"
        );
        assert!(
            render
                .array_access_for_op(0x401000, 5, false, 0, 4, Some(4))
                .is_none(),
            "wrong op site must not authorize array rendering"
        );
        assert!(
            render
                .array_access_for_op(0x401000, 4, true, 0, 4, Some(4))
                .is_none(),
            "wrong direction must not authorize array rendering"
        );
        assert!(
            render
                .array_access_for_op(0x401000, 4, false, 4, 4, Some(4))
                .is_none(),
            "wrong field offset must not authorize array rendering"
        );
        assert!(
            render
                .array_access_for_op(0x401000, 4, false, 0, 8, Some(4))
                .is_none(),
            "wrong stride must not authorize array rendering"
        );
        assert!(
            render
                .array_access_for_op(0x401000, 4, false, 0, 4, Some(8))
                .is_none(),
            "wrong access width must not authorize array rendering"
        );

        let mut wrong_object = render.clone();
        wrong_object
            .array_accesses_by_op
            .get_mut(&(0x401000, 4, false))
            .expect("array fact")
            .first_mut()
            .expect("array fact")
            .object = r2ssa::ObjectId(9);
        assert!(
            wrong_object
                .array_access_for_op(0x401000, 4, false, 0, 4, Some(4))
                .is_none(),
            "wrong object identity must not authorize array rendering"
        );

        let mut wrong_access = render.clone();
        wrong_access
            .array_accesses_by_op
            .get_mut(&(0x401000, 4, false))
            .expect("array fact")
            .first_mut()
            .expect("array fact")
            .access = other_access;
        assert!(
            wrong_access
                .array_access_for_op(0x401000, 4, false, 0, 4, Some(4))
                .is_none(),
            "wrong memory-access identity must not authorize array rendering"
        );
    }

    #[test]
    fn function_facts_authorizes_recovered_stack_owner_only_by_exact_object_offset_and_name() {
        let object = r2ssa::ObjectId(21);
        let facts = FunctionFacts::default().with_render(FunctionRenderFacts {
            stack_slot_offsets: BTreeMap::from([(object, -4)]),
            ..FunctionRenderFacts::default()
        });

        let authorization = facts
            .authorized_recovered_stack_slot_owner_render(object, -4, "i")
            .expect("a recovered loop scalar with exact object and offset should authorize");
        assert_eq!(authorization.object, object);
        assert_eq!(authorization.offset, -4);
        assert_eq!(authorization.name, "i");
        assert!(
            facts
                .authorized_recovered_stack_slot_owner_render(r2ssa::ObjectId(22), -4, "i")
                .is_none(),
            "wrong object must not authorize recovered stack owner rendering"
        );
        assert!(
            facts
                .authorized_recovered_stack_slot_owner_render(object, 4, "i")
                .is_none(),
            "wrong offset must not authorize recovered stack owner rendering"
        );
        for placeholder in ["fake_stack_slot", "local_4", "var_4h", "stack_8"] {
            assert!(
                facts
                    .authorized_recovered_stack_slot_owner_render(object, -4, placeholder)
                    .is_none(),
                "placeholder name {placeholder} must not authorize recovered stack owner rendering"
            );
        }
    }

    #[test]
    fn function_facts_authorizes_stack_param_owner_render_only_for_params() {
        let object = r2ssa::ObjectId(13);
        let facts = FunctionFacts::new(
            FunctionTypeFacts {
                visible_bindings: vec![
                    crate::VisibleBinding {
                        name: "stack_arg".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 64,
                            signedness: crate::Signedness::Signed,
                        }),
                        kind: VisibleBindingKind::Param,
                        stack_slot: Some(StackSlotKey {
                            base: ExternalStackBase::StackPointer,
                            offset: 8,
                        }),
                        param_index: Some(6),
                        source_reg: None,
                    },
                    crate::VisibleBinding {
                        name: "local_alias".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 64,
                            signedness: crate::Signedness::Signed,
                        }),
                        kind: VisibleBindingKind::Local,
                        stack_slot: Some(StackSlotKey {
                            base: ExternalStackBase::StackPointer,
                            offset: 8,
                        }),
                        param_index: None,
                        source_reg: None,
                    },
                ],
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(FunctionRenderFacts {
            stack_slot_offsets: BTreeMap::from([(object, 8)]),
            ..FunctionRenderFacts::default()
        });

        let authorization = facts
            .authorized_stack_param_owner_render(object, 8)
            .expect("typed parameter binding plus exact render object should authorize owner");
        assert_eq!(authorization.object, object);
        assert_eq!(authorization.offset, 8);
        assert_eq!(authorization.name, "stack_arg");
        assert!(
            facts
                .authorized_stack_param_owner_render(r2ssa::ObjectId(14), 8)
                .is_none(),
            "the stack parameter path still requires the exact render object"
        );
        assert!(
            facts
                .authorized_stack_param_owner_render(object, -8)
                .is_none(),
            "the stack parameter path still requires the exact offset"
        );

        let ambiguous = FunctionFacts::new(
            FunctionTypeFacts {
                visible_bindings: vec![
                    crate::VisibleBinding {
                        name: "left".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 64,
                            signedness: crate::Signedness::Signed,
                        }),
                        kind: VisibleBindingKind::Param,
                        stack_slot: Some(StackSlotKey {
                            base: ExternalStackBase::StackPointer,
                            offset: 8,
                        }),
                        param_index: Some(6),
                        source_reg: None,
                    },
                    crate::VisibleBinding {
                        name: "right".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 64,
                            signedness: crate::Signedness::Signed,
                        }),
                        kind: VisibleBindingKind::Param,
                        stack_slot: Some(StackSlotKey {
                            base: ExternalStackBase::StackPointer,
                            offset: 8,
                        }),
                        param_index: Some(6),
                        source_reg: None,
                    },
                ],
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(FunctionRenderFacts {
            stack_slot_offsets: BTreeMap::from([(object, 8)]),
            ..FunctionRenderFacts::default()
        });
        assert!(
            ambiguous
                .authorized_stack_param_owner_render(object, 8)
                .is_none(),
            "ambiguous typed parameter names at one stack offset must not be rendered"
        );

        let canonical_slot = FunctionFacts::new(
            FunctionTypeFacts {
                visible_bindings: vec![crate::VisibleBinding {
                    name: "arg6".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 64,
                        signedness: crate::Signedness::Signed,
                    }),
                    kind: VisibleBindingKind::Param,
                    stack_slot: Some(StackSlotKey {
                        base: ExternalStackBase::StackPointer,
                        offset: 8,
                    }),
                    param_index: Some(6),
                    source_reg: None,
                }],
                stack_slots: BTreeMap::from([(
                    StackSlotKey {
                        base: ExternalStackBase::StackPointer,
                        offset: 8,
                    },
                    crate::ExternalStackSlotSpec {
                        name: "arg_8h".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 64,
                            signedness: crate::Signedness::Signed,
                        }),
                        base: ExternalStackBase::StackPointer,
                        role: ExternalStackSlotRole::StackArg,
                        param_index: Some(6),
                        param_name: Some("arg7".to_string()),
                        source_reg: None,
                    },
                )]),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(FunctionRenderFacts {
            stack_slot_offsets: BTreeMap::from([(object, 8)]),
            ..FunctionRenderFacts::default()
        });
        let authorization = canonical_slot
            .authorized_stack_param_owner_render(object, 8)
            .expect("canonical stack slot name should authorize");
        assert_eq!(authorization.name, "arg7");

        let param_home = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(FunctionSignatureSpec {
                    ret_type: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: crate::Signedness::Signed,
                    }),
                    params: vec![FunctionParamSpec {
                        name: "node".to_string(),
                        ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Struct(
                            "Node".to_string(),
                        )))),
                    }],
                }),
                stack_slots: BTreeMap::from([(
                    StackSlotKey {
                        base: ExternalStackBase::FramePointer,
                        offset: 8,
                    },
                    crate::ExternalStackSlotSpec {
                        name: "node_home".to_string(),
                        ty: None,
                        base: ExternalStackBase::FramePointer,
                        role: ExternalStackSlotRole::ParamHome,
                        param_index: Some(0),
                        param_name: Some("node".to_string()),
                        source_reg: Some("rdi".to_string()),
                    },
                )]),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(FunctionRenderFacts {
            stack_slot_offsets: BTreeMap::from([(object, -8)]),
            ..FunctionRenderFacts::default()
        });
        let authorization = param_home
            .authorized_stack_param_owner_render(object, -8)
            .expect("typed parameter home should authorize original parameter owner");
        assert_eq!(authorization.name, "node");
        let raw_offset_param_home = param_home.clone().with_render(FunctionRenderFacts {
            stack_slot_offsets: BTreeMap::from([(object, 8)]),
            ..FunctionRenderFacts::default()
        });
        assert!(
            raw_offset_param_home
                .authorized_stack_param_owner_render(object, 8)
                .is_none(),
            "frame-pointer parameter homes must match the canonical rendered offset, not the raw slot sign"
        );
        assert!(
            param_home
                .authorized_stack_slot_owner_render(object, -8, "node_home")
                .is_none(),
            "hidden parameter-home storage name must not become a rendered owner"
        );
    }

    #[test]
    fn stack_owner_render_by_offset_rejects_ambiguous_or_untyped_slots() {
        let typed_slot = (
            StackSlotKey {
                base: ExternalStackBase::StackPointer,
                offset: -8,
            },
            crate::ExternalStackSlotSpec {
                name: "local_buf".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: crate::Signedness::Signed,
                }),
                role: ExternalStackSlotRole::Local,
                ..crate::ExternalStackSlotSpec::default()
            },
        );
        let ambiguous = FunctionFacts::new(
            FunctionTypeFacts {
                stack_slots: BTreeMap::from([typed_slot.clone()]),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(FunctionRenderFacts {
            stack_slot_offsets: BTreeMap::from([
                (r2ssa::ObjectId(1), -8),
                (r2ssa::ObjectId(2), -8),
            ]),
            ..FunctionRenderFacts::default()
        });
        assert!(
            ambiguous
                .authorized_stack_slot_owner_render_by_offset(-8, "local_buf")
                .is_none(),
            "offset-only bridge must refuse duplicate render objects"
        );

        let unknown_role = FunctionFacts::new(
            FunctionTypeFacts {
                stack_slots: BTreeMap::from([(
                    typed_slot.0.clone(),
                    crate::ExternalStackSlotSpec {
                        role: ExternalStackSlotRole::Unknown,
                        ..typed_slot.1.clone()
                    },
                )]),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(FunctionRenderFacts {
            stack_slot_offsets: BTreeMap::from([(r2ssa::ObjectId(3), -8)]),
            ..FunctionRenderFacts::default()
        });
        assert!(
            unknown_role
                .authorized_stack_slot_owner_render_by_offset(-8, "local_buf")
                .is_none(),
            "unknown stack-slot roles are not enough for certified owner rendering"
        );

        let untyped = FunctionFacts::new(
            FunctionTypeFacts {
                stack_slots: BTreeMap::from([(
                    typed_slot.0,
                    crate::ExternalStackSlotSpec {
                        ty: Some(CTypeLike::Unknown),
                        ..typed_slot.1
                    },
                )]),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(FunctionRenderFacts {
            stack_slot_offsets: BTreeMap::from([(r2ssa::ObjectId(4), -8)]),
            ..FunctionRenderFacts::default()
        });
        assert!(
            untyped
                .authorized_stack_slot_owner_render_by_offset(-8, "local_buf")
                .is_none(),
            "unknown types are not enough for certified owner rendering"
        );
    }

    #[test]
    fn decompile_type_override_requires_render_authorized_signature() {
        let base_signature = crate::FunctionSignatureSpec {
            ret_type: Some(crate::CTypeLike::Void),
            params: Vec::new(),
        };
        let override_signature = crate::FunctionSignatureSpec {
            ret_type: Some(crate::CTypeLike::Int {
                bits: 64,
                signedness: crate::Signedness::Unsigned,
            }),
            params: vec![crate::FunctionParamSpec {
                name: "buf".to_string(),
                ty: Some(crate::CTypeLike::Pointer(Box::new(crate::CTypeLike::Int {
                    bits: 8,
                    signedness: crate::Signedness::Unsigned,
                }))),
            }],
        };
        let mut facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(base_signature.clone()),
                signature_certificate: crate::SignatureCertificate::from_signature(
                    &base_signature,
                    [crate::SignatureCertificateSource::ExternalContext],
                ),
                ..FunctionTypeFacts::default()
            },
            None,
        );

        assert!(!facts.apply_decompile_type_override(FunctionTypeFacts {
            merged_signature: Some(override_signature.clone()),
            signature_certificate: None,
            ..FunctionTypeFacts::default()
        }));
        assert_eq!(
            facts.types.render_authorized_signature(),
            Some(&base_signature)
        );

        assert!(facts.apply_decompile_type_override(FunctionTypeFacts {
            merged_signature: Some(override_signature.clone()),
            signature_certificate: crate::SignatureCertificate::from_signature(
                &override_signature,
                [crate::SignatureCertificateSource::ExternalContext],
            ),
            ..FunctionTypeFacts::default()
        }));
        assert_eq!(
            facts.types.render_authorized_signature(),
            Some(&override_signature)
        );
    }

    #[test]
    fn decompile_fallback_comment_requires_fallback_route() {
        let fallback = DecompileRouteFacts {
            kind: DecompileRouteKind::FallbackComment,
            reason: Some("typed refusal".to_string()),
            fallback_comment: Some("/* typed fallback */".to_string()),
            skip_runtime_type_inference: true,
            use_prepared_semantic_view: false,
            proof_coverage: r2sym::ProofCoverage::default(),
            render_permission: r2sym::RenderPermission::refuse(
                r2sym::ProofOwner::R2engine,
                "typed refusal",
            ),
        };
        let standard_with_comment = DecompileRouteFacts {
            kind: DecompileRouteKind::Standard,
            reason: Some("must not render".to_string()),
            fallback_comment: Some("/* wrong route */".to_string()),
            skip_runtime_type_inference: false,
            use_prepared_semantic_view: false,
            proof_coverage: r2sym::ProofCoverage::default(),
            render_permission: r2sym::RenderPermission::certified(
                r2sym::ProofOwner::R2engine,
                "standard route",
            ),
        };

        assert_eq!(
            FunctionFacts::default()
                .with_decompile_route(fallback)
                .decompile_fallback_comment(),
            Some("/* typed fallback */")
        );
        assert_eq!(
            FunctionFacts::default()
                .with_decompile_route(standard_with_comment)
                .decompile_fallback_comment(),
            None,
            "fallback comments are refusal payloads, not a side channel on executable routes"
        );
    }

    fn summary_with_effects(id: r2ssa::InterprocFunctionId) -> r2ssa::FunctionSemanticSummary {
        let mut summary = r2ssa::FunctionSemanticSummary::unknown(id, Some("sym.effect".into()));
        summary.arg_effects.insert(
            0,
            r2ssa::SummaryArgEffect {
                escape: true,
                ..r2ssa::SummaryArgEffect::default()
            },
        );
        summary.arg_effects.insert(
            1,
            r2ssa::SummaryArgEffect {
                write: true,
                ..r2ssa::SummaryArgEffect::default()
            },
        );
        summary.memory_effects.push(r2ssa::SummaryMemoryEffect {
            kind: r2ssa::SummaryMemoryEffectKind::Write,
            location: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 2 },
                range: None,
            },
        });
        summary.memory_effects.push(r2ssa::SummaryMemoryEffect {
            kind: r2ssa::SummaryMemoryEffectKind::Escape,
            location: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 5 },
                range: None,
            },
        });
        summary.transfer_effects.push(r2ssa::SummaryTransferEffect {
            dst: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 3 },
                range: None,
            },
            src: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 4 },
                range: None,
            },
            len: r2ssa::SummaryTransferLength::Unknown,
        });
        summary
    }

    #[test]
    fn summary_rollup_out_params_require_writeback_evidence() {
        let root = r2ssa::InterprocFunctionId(0x401000);
        let helper = r2ssa::InterprocFunctionId(0x402000);
        let set = r2ssa::InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([
                (root, summary_with_effects(root)),
                (helper, summary_with_effects(helper)),
            ]),
            diagnostics: Default::default(),
        };

        let view = InterprocSummaryView::new(Some(set));

        assert_eq!(view.out_param_indices(), vec![1, 2, 3]);
        assert_eq!(
            view.rollup
                .as_ref()
                .expect("rollup")
                .out_param_facts
                .iter()
                .map(|fact| (&fact.evidence, &fact.source))
                .collect::<Vec<_>>(),
            vec![
                (
                    &OutParamCertificateEvidence::InterprocArgWrite,
                    &OutParamCertificateSource::InterprocSummaryEffect {
                        function_id: root.0,
                        evidence: OutParamCertificateEvidence::InterprocArgWrite,
                        param_index: 1,
                        effect_index: 1,
                    },
                ),
                (
                    &OutParamCertificateEvidence::InterprocMemoryWrite,
                    &OutParamCertificateSource::InterprocSummaryEffect {
                        function_id: root.0,
                        evidence: OutParamCertificateEvidence::InterprocMemoryWrite,
                        param_index: 2,
                        effect_index: 0,
                    },
                ),
                (
                    &OutParamCertificateEvidence::InterprocTransferDst,
                    &OutParamCertificateSource::InterprocSummaryEffect {
                        function_id: root.0,
                        evidence: OutParamCertificateEvidence::InterprocTransferDst,
                        param_index: 3,
                        effect_index: 0,
                    },
                ),
            ]
        );
        assert_eq!(view.pointer_param_indices(), &[0, 1, 2, 3, 4, 5]);
        let helper_view = view
            .helper_view_for_name("sym.effect")
            .expect("helper view");
        assert_eq!(
            out_param_indices_from_facts(&helper_view.out_param_facts),
            vec![1, 2, 3]
        );
        assert_eq!(helper_view.pointer_param_indices, vec![0, 1, 2, 3, 4, 5]);
    }
}
