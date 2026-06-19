use std::cell::{Cell, OnceCell};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::OnceLock;

use crate::analysis;
use crate::ast::CType;
use r2ssa::{
    CallSiteFacts, FunctionSSABlock, InterprocSummarySet, MemorySSAFacts, ObjectModel,
    PredicateFacts, SSAVar, SsaArtifact, ValueId,
};
#[cfg(test)]
use r2types::ExternalStackVarSpec;
use r2types::{
    CalleeFact, CalleeResolutionFacts, ExternalStackSlotSpec, ExternalTypeDb, FunctionType,
    InterprocSummaryView, SignatureRegistry, StackSlotKey, TypeOracle, VisibleBinding,
};

pub(crate) type SSABlock = FunctionSSABlock;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ResolutionPhase {
    Semantic,
    Definition,
    DefinitionRaw,
    Visible,
    ImportedArg,
    Memory,
    Return,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ResolutionGuardKey {
    pub(crate) phase: ResolutionPhase,
    pub(crate) name: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum EffectRenderProofKind {
    Call,
    Expression,
    MemoryRead,
    MemoryWrite,
    Return,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct EffectRenderProof {
    pub(crate) kind: EffectRenderProofKind,
    pub(crate) block_addr: u64,
    pub(crate) op_idx: usize,
    pub(crate) target: Option<ValueId>,
    pub(crate) address: Option<ValueId>,
    pub(crate) value: Option<ValueId>,
    pub(crate) values: Vec<ValueId>,
    pub(crate) materialized_phi_copy: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct PtrArith {
    pub(crate) base: SSAVar,
    pub(crate) index: SSAVar,
    pub(crate) element_size: u32,
    pub(crate) is_sub: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct FoldArchConfig {
    pub(crate) ptr_size: u32,
    pub(crate) sp_name: String,
    pub(crate) fp_name: String,
    pub(crate) ret_reg_name: String,
    pub(crate) arg_regs: Vec<String>,
    pub(crate) caller_saved_regs: HashSet<String>,
}

#[derive(Clone, Copy)]
pub(crate) struct FoldInputs<'a> {
    pub(crate) arch: &'a FoldArchConfig,
    pub(crate) function_names: &'a HashMap<u64, String>,
    pub(crate) strings: &'a HashMap<u64, String>,
    pub(crate) symbols: &'a HashMap<u64, String>,
    pub(crate) known_function_signatures: &'a HashMap<String, FunctionType>,
    pub(crate) callee_facts: &'a BTreeMap<u64, CalleeFact>,
    pub(crate) callee_resolution: Option<&'a CalleeResolutionFacts>,
    pub(crate) stack_slots: &'a BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    #[cfg(test)]
    pub(crate) external_stack_vars: &'a HashMap<i64, ExternalStackVarSpec>,
    pub(crate) visible_bindings: &'a [VisibleBinding],
    pub(crate) external_type_db: &'a ExternalTypeDb,
    pub(crate) semantic_artifact: Option<&'a r2sym::SemanticArtifact>,
    pub(crate) param_register_aliases: &'a HashMap<String, String>,
    pub(crate) type_hints: &'a HashMap<String, CType>,
    pub(crate) type_oracle: Option<&'a dyn TypeOracle>,
    pub(crate) function_return_type: Option<&'a CType>,
    pub(crate) prepared_ssa: Option<&'a SsaArtifact>,
    pub(crate) interproc_summary_set: Option<&'a InterprocSummarySet>,
    pub(crate) summary_view: Option<&'a InterprocSummaryView>,
    pub(crate) prepared_semantic_view: Option<&'a analysis::PreparedSemanticView>,
    pub(crate) prepared_objects: Option<&'a ObjectModel>,
    #[allow(dead_code)]
    pub(crate) prepared_memory: Option<&'a MemorySSAFacts>,
    pub(crate) prepared_predicates: Option<&'a PredicateFacts>,
    pub(crate) prepared_call_sites: Option<&'a CallSiteFacts>,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct FoldState {
    pub(crate) analysis_ctx: analysis::DecompilerFacts,
    pub(crate) exit_block: Option<u64>,
    pub(crate) return_blocks: HashSet<u64>,
    pub(crate) return_stack_slots: HashSet<i64>,
}

pub struct FoldingContext<'a> {
    pub(crate) inputs: FoldInputs<'a>,
    pub(crate) state: FoldState,
    pub(crate) current_block_addr: Cell<Option<u64>>,
    pub(crate) current_op_idx: Cell<Option<usize>>,
    pub(crate) hide_stack_frame: bool,
    pub(crate) userop_names: HashMap<u32, String>,
    pub(crate) signature_registry: SignatureRegistry,
    pub(crate) rendered_alias_lookup_cache: std::cell::RefCell<HashMap<String, Option<String>>>,
    pub(crate) preferred_entry_arg_lookup_cache:
        std::cell::RefCell<HashMap<String, Option<String>>>,
    pub(crate) forwarded_source_cache: std::cell::RefCell<HashMap<String, Option<r2ssa::SSAVar>>>,
    pub(crate) call_result_owner_name_cache:
        std::cell::RefCell<BTreeMap<(u64, usize), Option<String>>>,
    pub(crate) call_result_owner_expr_cache:
        std::cell::RefCell<HashMap<String, Option<crate::ast::CExpr>>>,
    pub(crate) non_variadic_call_arity_cache: std::cell::RefCell<HashMap<String, Option<usize>>>,
    pub(crate) authoritative_source_args_cache:
        std::cell::RefCell<BTreeMap<(u64, usize), Vec<crate::ast::CExpr>>>,
    pub(crate) owned_call_visible_names_cache: std::cell::RefCell<Option<HashSet<String>>>,
    pub(crate) prepared_semantic_view_cache: OnceCell<analysis::PreparedSemanticView>,
    pub(crate) prepared_semantic_view_building: Cell<bool>,
    pub(crate) semantic_render_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) value_render_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) definition_lookup_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) definition_raw_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) resolution_guard: std::cell::RefCell<HashSet<ResolutionGuardKey>>,
    pub(crate) effect_render_proofs: std::cell::RefCell<Vec<EffectRenderProof>>,
}

impl FoldArchConfig {
    pub(crate) fn for_ptr_size(ptr_size: u32) -> Self {
        let sp_name = if ptr_size == 64 {
            "rsp".to_string()
        } else {
            "esp".to_string()
        };
        let fp_name = if ptr_size == 64 {
            "rbp".to_string()
        } else {
            "ebp".to_string()
        };
        let ret_reg_name = if ptr_size == 64 {
            "rax".to_string()
        } else {
            "eax".to_string()
        };
        let arg_regs = if ptr_size == 64 {
            vec![
                "rdi".to_string(),
                "rsi".to_string(),
                "rdx".to_string(),
                "rcx".to_string(),
                "r8".to_string(),
                "r9".to_string(),
            ]
        } else {
            vec![]
        };
        let caller_saved_regs = {
            let mut regs = HashSet::new();
            if ptr_size == 64 {
                for r in ["rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"] {
                    regs.insert(r.to_string());
                }
            } else {
                for r in ["eax", "ecx", "edx"] {
                    regs.insert(r.to_string());
                }
            }
            regs
        };

        Self {
            ptr_size,
            sp_name,
            fp_name,
            ret_reg_name,
            arg_regs,
            caller_saved_regs,
        }
    }
}

impl<'a> FoldingContext<'a> {
    pub(crate) fn from_inputs(inputs: FoldInputs<'a>) -> Self {
        Self {
            inputs,
            state: FoldState::default(),
            current_block_addr: Cell::new(None),
            current_op_idx: Cell::new(None),
            hide_stack_frame: true,
            userop_names: HashMap::new(),
            signature_registry: SignatureRegistry::from_embedded_json(),
            rendered_alias_lookup_cache: std::cell::RefCell::new(HashMap::new()),
            preferred_entry_arg_lookup_cache: std::cell::RefCell::new(HashMap::new()),
            forwarded_source_cache: std::cell::RefCell::new(HashMap::new()),
            call_result_owner_name_cache: std::cell::RefCell::new(BTreeMap::new()),
            call_result_owner_expr_cache: std::cell::RefCell::new(HashMap::new()),
            non_variadic_call_arity_cache: std::cell::RefCell::new(HashMap::new()),
            authoritative_source_args_cache: std::cell::RefCell::new(BTreeMap::new()),
            owned_call_visible_names_cache: std::cell::RefCell::new(None),
            prepared_semantic_view_cache: OnceCell::new(),
            prepared_semantic_view_building: Cell::new(false),
            semantic_render_in_progress: std::cell::RefCell::new(HashSet::new()),
            value_render_in_progress: std::cell::RefCell::new(HashSet::new()),
            definition_lookup_in_progress: std::cell::RefCell::new(HashSet::new()),
            definition_raw_in_progress: std::cell::RefCell::new(HashSet::new()),
            resolution_guard: std::cell::RefCell::new(HashSet::new()),
            effect_render_proofs: std::cell::RefCell::new(Vec::new()),
        }
    }

    pub(crate) fn clear_effect_render_proofs(&self) {
        self.effect_render_proofs.borrow_mut().clear();
    }

    pub(crate) fn effect_render_proofs(&self) -> Vec<EffectRenderProof> {
        self.effect_render_proofs.borrow().clone()
    }

    pub(crate) fn record_effect_render_proof_for_values(
        &self,
        kind: EffectRenderProofKind,
        block_addr: u64,
        op_idx: usize,
        target: Option<ValueId>,
        values: Vec<ValueId>,
    ) {
        self.effect_render_proofs
            .borrow_mut()
            .push(EffectRenderProof {
                kind,
                block_addr,
                op_idx,
                target,
                address: None,
                value: None,
                values,
                materialized_phi_copy: false,
            });
    }

    pub(crate) fn record_effect_render_proof_for_value(
        &self,
        kind: EffectRenderProofKind,
        block_addr: u64,
        op_idx: usize,
        value: Option<ValueId>,
    ) {
        self.effect_render_proofs
            .borrow_mut()
            .push(EffectRenderProof {
                kind,
                block_addr,
                op_idx,
                target: None,
                address: None,
                value,
                values: Vec::new(),
                materialized_phi_copy: false,
            });
    }

    pub(crate) fn record_effect_render_proof_for_materialized_phi_copy(
        &self,
        block_addr: u64,
        op_idx: usize,
        value: Option<ValueId>,
    ) {
        self.effect_render_proofs
            .borrow_mut()
            .push(EffectRenderProof {
                kind: EffectRenderProofKind::Expression,
                block_addr,
                op_idx,
                target: None,
                address: None,
                value,
                values: Vec::new(),
                materialized_phi_copy: true,
            });
    }

    pub(crate) fn record_effect_render_proof_for_memory(
        &self,
        kind: EffectRenderProofKind,
        block_addr: u64,
        op_idx: usize,
        address: ValueId,
        value: Option<ValueId>,
    ) {
        self.effect_render_proofs
            .borrow_mut()
            .push(EffectRenderProof {
                kind,
                block_addr,
                op_idx,
                target: None,
                address: Some(address),
                value,
                values: Vec::new(),
                materialized_phi_copy: false,
            });
    }

    /// Test convenience constructor.
    pub fn new(ptr_size: u32) -> Self {
        static EMPTY_U64_STRING: OnceLock<HashMap<u64, String>> = OnceLock::new();
        static EMPTY_STACK_SLOTS: OnceLock<BTreeMap<StackSlotKey, ExternalStackSlotSpec>> =
            OnceLock::new();
        #[cfg(test)]
        static EMPTY_I64_STACK: OnceLock<HashMap<i64, ExternalStackVarSpec>> = OnceLock::new();
        static EMPTY_VISIBLE_BINDINGS: OnceLock<Vec<VisibleBinding>> = OnceLock::new();
        static EMPTY_TYPE_DB: OnceLock<ExternalTypeDb> = OnceLock::new();
        static EMPTY_STRING_STRING: OnceLock<HashMap<String, String>> = OnceLock::new();
        static EMPTY_STRING_FNTY: OnceLock<HashMap<String, FunctionType>> = OnceLock::new();
        static EMPTY_CALLEE_FACTS: OnceLock<BTreeMap<u64, CalleeFact>> = OnceLock::new();
        static EMPTY_STRING_CTYPE: OnceLock<HashMap<String, CType>> = OnceLock::new();
        static ARCH64: OnceLock<FoldArchConfig> = OnceLock::new();
        static ARCH32: OnceLock<FoldArchConfig> = OnceLock::new();

        let arch = match ptr_size {
            64 => ARCH64.get_or_init(|| FoldArchConfig::for_ptr_size(64)),
            32 => ARCH32.get_or_init(|| FoldArchConfig::for_ptr_size(32)),
            other => Box::leak(Box::new(FoldArchConfig::for_ptr_size(other))),
        };

        let inputs = FoldInputs {
            arch,
            function_names: EMPTY_U64_STRING.get_or_init(HashMap::new),
            strings: EMPTY_U64_STRING.get_or_init(HashMap::new),
            symbols: EMPTY_U64_STRING.get_or_init(HashMap::new),
            known_function_signatures: EMPTY_STRING_FNTY.get_or_init(HashMap::new),
            callee_facts: EMPTY_CALLEE_FACTS.get_or_init(BTreeMap::new),
            callee_resolution: None,
            stack_slots: EMPTY_STACK_SLOTS.get_or_init(BTreeMap::new),
            #[cfg(test)]
            external_stack_vars: EMPTY_I64_STACK.get_or_init(HashMap::new),
            visible_bindings: EMPTY_VISIBLE_BINDINGS.get_or_init(Vec::new),
            external_type_db: EMPTY_TYPE_DB.get_or_init(ExternalTypeDb::default),
            semantic_artifact: None,
            param_register_aliases: EMPTY_STRING_STRING.get_or_init(HashMap::new),
            type_hints: EMPTY_STRING_CTYPE.get_or_init(HashMap::new),
            type_oracle: None,
            function_return_type: None,
            prepared_ssa: None,
            interproc_summary_set: None,
            summary_view: None,
            prepared_semantic_view: None,
            prepared_objects: None,
            prepared_memory: None,
            prepared_predicates: None,
            prepared_call_sites: None,
        };

        Self::from_inputs(inputs)
    }
}
