use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

use crate::analysis;
use crate::ast::CType;
use r2ssa::{FunctionSSABlock, SSAVar};
use r2types::{ExternalStackVarSpec, ExternalTypeDb, FunctionType, SignatureRegistry, TypeOracle};

pub(crate) type SSABlock = FunctionSSABlock;

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
    pub(crate) external_stack_vars: &'a HashMap<i64, ExternalStackVarSpec>,
    pub(crate) external_type_db: &'a ExternalTypeDb,
    pub(crate) param_register_aliases: &'a HashMap<String, String>,
    pub(crate) type_hints: &'a HashMap<String, CType>,
    pub(crate) type_oracle: Option<&'a dyn TypeOracle>,
    pub(crate) function_return_type: Option<&'a CType>,
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
    pub(crate) hide_stack_frame: bool,
    pub(crate) userop_names: HashMap<u32, String>,
    pub(crate) signature_registry: SignatureRegistry,
    pub(crate) rendered_alias_lookup_cache: std::cell::RefCell<HashMap<String, Option<String>>>,
    pub(crate) preferred_entry_arg_lookup_cache:
        std::cell::RefCell<HashMap<String, Option<String>>>,
    pub(crate) forwarded_source_cache: std::cell::RefCell<HashMap<String, Option<r2ssa::SSAVar>>>,
    pub(crate) semantic_render_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) value_render_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) definition_lookup_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) definition_raw_in_progress: std::cell::RefCell<HashSet<String>>,
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
            hide_stack_frame: true,
            userop_names: HashMap::new(),
            signature_registry: SignatureRegistry::from_embedded_json(),
            rendered_alias_lookup_cache: std::cell::RefCell::new(HashMap::new()),
            preferred_entry_arg_lookup_cache: std::cell::RefCell::new(HashMap::new()),
            forwarded_source_cache: std::cell::RefCell::new(HashMap::new()),
            semantic_render_in_progress: std::cell::RefCell::new(HashSet::new()),
            value_render_in_progress: std::cell::RefCell::new(HashSet::new()),
            definition_lookup_in_progress: std::cell::RefCell::new(HashSet::new()),
            definition_raw_in_progress: std::cell::RefCell::new(HashSet::new()),
        }
    }

    /// Test convenience constructor.
    pub fn new(ptr_size: u32) -> Self {
        static EMPTY_U64_STRING: OnceLock<HashMap<u64, String>> = OnceLock::new();
        static EMPTY_I64_STACK: OnceLock<HashMap<i64, ExternalStackVarSpec>> = OnceLock::new();
        static EMPTY_TYPE_DB: OnceLock<ExternalTypeDb> = OnceLock::new();
        static EMPTY_STRING_STRING: OnceLock<HashMap<String, String>> = OnceLock::new();
        static EMPTY_STRING_FNTY: OnceLock<HashMap<String, FunctionType>> = OnceLock::new();
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
            external_stack_vars: EMPTY_I64_STACK.get_or_init(HashMap::new),
            external_type_db: EMPTY_TYPE_DB.get_or_init(ExternalTypeDb::default),
            param_register_aliases: EMPTY_STRING_STRING.get_or_init(HashMap::new),
            type_hints: EMPTY_STRING_CTYPE.get_or_init(HashMap::new),
            type_oracle: None,
            function_return_type: None,
        };

        Self::from_inputs(inputs)
    }
}
