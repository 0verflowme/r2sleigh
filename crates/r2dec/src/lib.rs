//! r2dec - Decompiler for r2sleigh.
//!
//! This crate provides decompilation capabilities for the r2sleigh project,
//! converting SSA form to readable C code.
//!
//! ## Overview
//!
//! The decompilation pipeline consists of:
//!
//! 1. **AST** (`ast`): C Abstract Syntax Tree representation
//! 2. **Expression Building** (`expr`): Convert SSA operations to C expressions
//! 3. **Region Identification** (`region`): Identify control flow regions
//! 4. **Control Flow Structuring** (`structure`): Convert CFG to structured code
//! 5. **Type Facts** (`r2types`): Consume inferred type/layout facts
//! 6. **Variable Recovery** (`variable`): Recover variable names and types
//! 7. **Code Generation** (`codegen`): Generate readable C source code
//!
//! ## Usage
//!
//! ```ignore
//! use r2dec::{Decompiler, DecompilerConfig};
//! use r2ssa::SSAFunction;
//!
//! let func: SSAFunction = /* ... */;
//! let config = DecompilerConfig::default();
//! let decompiler = Decompiler::new(config);
//! let c_code = decompiler.decompile(&func);
//! println!("{}", c_code);
//! ```

pub(crate) mod address;
pub(crate) mod analysis;
pub mod ast;
pub mod codegen;
pub mod fold;
pub(crate) mod normalize;
pub(crate) mod post_rename;
pub mod region;
pub(crate) mod registers;
pub mod structure;
pub mod variable;

pub use ast::{BinaryOp, CExpr, CFunction, CStmt, CType, UnaryOp};
pub use codegen::{CodeGenConfig, CodeGenerator, generate};
pub use fold::lower_ssa_ops_to_stmts;
pub use region::{Region, RegionAnalyzer};
pub use structure::ControlFlowStructurer;
pub use variable::VariableRecovery;

use crate::fold::FoldingContext;
use crate::fold::context::{FoldArchConfig, FoldInputs};
use r2ssa::SSAFunction;
use r2ssa::SSAOp;
use r2types::{
    CTypeLike, ExternalRegisterParamSpec, ExternalTypeDb, FunctionSignatureSpec, FunctionType,
    FunctionTypeFacts, StackSlotKey, TypeInference, TypeOracle, VisibleBinding, VisibleBindingKind,
};
use std::collections::HashSet;

fn is_generic_arg_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower
        .strip_prefix("arg")
        .map(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
        .unwrap_or(false)
}

fn normalize_callee_name(name: &str) -> String {
    let mut out = name.trim().to_ascii_lowercase();
    for prefix in ["sym.imp.", "sym.", "fcn."] {
        if let Some(rest) = out.strip_prefix(prefix) {
            out = rest.to_string();
            break;
        }
    }
    if let Some((base, ver)) = out.rsplit_once('_')
        && !base.is_empty()
        && ver.chars().all(|c| c.is_ascii_digit())
    {
        return base.to_string();
    }
    out
}

fn should_skip_runtime_type_inference(prepared: Option<&r2ssa::PreparedFunctionSSA>) -> bool {
    let Some(prepared) = prepared else {
        return false;
    };
    let summary = prepared.function().cfg_risk_summary();
    summary.block_count >= 96
        && summary.switch_block_count > 0
        && summary.max_switch_cases >= 32
        && summary.back_edge_count == 0
}

fn should_use_prepared_semantic_view(prepared: Option<&r2ssa::PreparedFunctionSSA>) -> bool {
    prepared.is_some()
}

fn seed_runtime_type_hints_from_facts_and_recovery(
    type_facts: &FunctionTypeFacts,
    var_recovery: &VariableRecovery,
) -> std::collections::HashMap<String, CType> {
    let mut type_hints = std::collections::HashMap::new();
    let mut insert = |name: &str, ty: &CType| {
        if matches!(ty, CType::Unknown | CType::Void) {
            return;
        }
        type_hints.insert(name.to_string(), ty.clone());
        type_hints.insert(name.to_ascii_lowercase(), ty.clone());
    };

    for var in var_recovery.parameters() {
        insert(&var.name, &var.ty);
    }
    for var in var_recovery.locals() {
        insert(&var.name, &var.ty);
    }
    for binding in &type_facts.visible_bindings {
        if let Some(ty) = binding.ty.as_ref() {
            insert(&binding.name, &type_like_to_ctype(ty));
        }
    }
    for reg_param in &type_facts.register_params {
        if let Some(ty) = reg_param.ty.as_ref() {
            insert(&reg_param.name, &type_like_to_ctype(ty));
        }
    }
    for slot in type_facts.stack_slots.values() {
        if let Some(ty) = slot.ty.as_ref() {
            insert(&slot.name, &type_like_to_ctype(ty));
        }
    }

    type_hints
}

#[cfg_attr(not(test), allow(dead_code))]
fn ctype_to_type_like(ty: &CType) -> CTypeLike {
    match ty {
        CType::Void => CTypeLike::Void,
        CType::Bool => CTypeLike::Bool,
        CType::Int(bits) => CTypeLike::Int {
            bits: *bits,
            signedness: r2types::Signedness::Signed,
        },
        CType::UInt(bits) => CTypeLike::Int {
            bits: *bits,
            signedness: r2types::Signedness::Unsigned,
        },
        CType::Float(bits) => CTypeLike::Float(*bits),
        CType::Pointer(inner) => CTypeLike::Pointer(Box::new(ctype_to_type_like(inner))),
        CType::Array(inner, len) => CTypeLike::Array(Box::new(ctype_to_type_like(inner)), *len),
        CType::Struct(name) => CTypeLike::Struct(name.clone()),
        CType::Union(name) => CTypeLike::Union(name.clone()),
        CType::Enum(name) => CTypeLike::Enum(name.clone()),
        CType::Function { .. } | CType::Typedef(_) | CType::Unknown => CTypeLike::Unknown,
    }
}

fn type_like_to_ctype(ty: &CTypeLike) -> CType {
    match ty {
        CTypeLike::Void => CType::Void,
        CTypeLike::Bool => CType::Bool,
        CTypeLike::Int { bits, signedness } => match signedness {
            r2types::Signedness::Unsigned => CType::UInt(*bits),
            _ => CType::Int(*bits),
        },
        CTypeLike::Float(bits) => CType::Float(*bits),
        CTypeLike::Pointer(inner) => CType::Pointer(Box::new(type_like_to_ctype(inner))),
        CTypeLike::Array(inner, len) => CType::Array(Box::new(type_like_to_ctype(inner)), *len),
        CTypeLike::Struct(name) => CType::Struct(name.clone()),
        CTypeLike::Union(name) => CType::Union(name.clone()),
        CTypeLike::Enum(name) => CType::Enum(name.clone()),
        CTypeLike::Function | CTypeLike::Unknown => CType::Unknown,
    }
}

fn merge_params_with_external_signature(
    recovered_params: Vec<ast::CParam>,
    signature: Option<&FunctionSignatureSpec>,
) -> Vec<ast::CParam> {
    let Some(signature) = signature else {
        return recovered_params;
    };

    if signature.params.is_empty() {
        return recovered_params;
    }

    let signature_is_authoritative = signature.ret_type.is_some()
        || signature
            .params
            .iter()
            .any(|param| param.ty.is_some() || !is_generic_arg_name(&param.name));
    let target_len = if signature_is_authoritative {
        signature.params.len()
    } else {
        recovered_params.len().max(signature.params.len())
    };
    (0..target_len)
        .map(|idx| {
            let fallback_name = format!("arg{}", idx + 1);
            let mut param = recovered_params.get(idx).cloned().unwrap_or(ast::CParam {
                ty: CType::Int(32),
                name: fallback_name,
            });

            if let Some(ext) = signature.params.get(idx) {
                if !is_generic_arg_name(&ext.name) {
                    param.name = ext.name.clone();
                }
                if let Some(ext_ty) = &ext.ty {
                    param.ty = type_like_to_ctype(ext_ty);
                }
            }

            param
        })
        .collect()
}

fn register_alias_names(reg_name: &str) -> Vec<String> {
    let lower = reg_name.trim().to_ascii_lowercase();
    if lower.is_empty() {
        return Vec::new();
    }

    match lower.as_str() {
        "rdi" | "edi" | "di" | "dil" => {
            return vec!["rdi", "edi", "di", "dil"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "rsi" | "esi" | "si" | "sil" => {
            return vec!["rsi", "esi", "si", "sil"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "rdx" | "edx" | "dx" | "dl" => {
            return vec!["rdx", "edx", "dx", "dl"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "rcx" | "ecx" | "cx" | "cl" => {
            return vec!["rcx", "ecx", "cx", "cl"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        _ => {}
    }

    for base in ["r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"] {
        if lower == base
            || lower == format!("{base}d")
            || lower == format!("{base}w")
            || lower == format!("{base}b")
        {
            return vec![
                base.to_string(),
                format!("{base}d"),
                format!("{base}w"),
                format!("{base}b"),
            ];
        }
    }

    if let Some(rest) = lower.strip_prefix('x')
        && rest.chars().all(|c| c.is_ascii_digit())
    {
        return vec![lower.clone(), format!("w{rest}")];
    }
    if let Some(rest) = lower.strip_prefix('w')
        && rest.chars().all(|c| c.is_ascii_digit())
    {
        return vec![format!("x{rest}"), lower];
    }

    vec![lower]
}

fn build_param_register_aliases(
    params: &[ast::CParam],
    recovered_params: &[(r2ssa::SSAVar, ast::CParam)],
    register_params: &[ExternalRegisterParamSpec],
    abi_arg_regs: &[String],
) -> std::collections::HashMap<String, String> {
    let mut aliases = std::collections::HashMap::new();

    for (idx, reg_name) in abi_arg_regs.iter().enumerate() {
        let Some(param) = params.get(idx) else {
            continue;
        };
        for alias in register_alias_names(reg_name) {
            aliases.insert(alias, param.name.clone());
        }
    }

    for (idx, (ssa_var, _)) in recovered_params.iter().enumerate() {
        if let Some(param) = params.get(idx) {
            aliases.insert(ssa_var.name.to_ascii_lowercase(), param.name.clone());
        }
    }

    for (idx, reg_param) in register_params.iter().enumerate() {
        let Some(param) = params.get(idx) else {
            continue;
        };
        for alias in register_alias_names(&reg_param.reg) {
            aliases.insert(alias, param.name.clone());
        }
    }

    aliases
}

/// Decompiler configuration.
#[derive(Debug, Clone)]
pub struct DecompilerConfig {
    /// Code generation configuration.
    pub codegen: CodeGenConfig,
    /// Pointer size in bits.
    pub ptr_size: u32,
    /// Stack pointer register name.
    pub sp_name: String,
    /// Frame pointer register name.
    pub fp_name: String,
    /// Ordered argument registers for the active ABI.
    pub arg_regs: Vec<String>,
    /// Return-value registers for the active ABI.
    pub ret_regs: Vec<String>,
    /// Caller-saved registers for the active ABI.
    pub caller_saved_regs: HashSet<String>,
    /// Soft cap for function blocks before forcing fallback.
    pub max_blocks: usize,
}

impl Default for DecompilerConfig {
    fn default() -> Self {
        Self {
            codegen: CodeGenConfig::default(),
            ptr_size: 64,
            sp_name: "rsp".to_string(),
            fp_name: "rbp".to_string(),
            arg_regs: vec![
                "rdi".to_string(),
                "rsi".to_string(),
                "rdx".to_string(),
                "rcx".to_string(),
                "r8".to_string(),
                "r9".to_string(),
            ],
            ret_regs: vec![
                "rax".to_string(),
                "eax".to_string(),
                "xmm0".to_string(),
                "xmm0_qa".to_string(),
                "xmm0_qb".to_string(),
                "st0".to_string(),
            ],
            caller_saved_regs: ["rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            max_blocks: 200,
        }
    }
}

impl DecompilerConfig {
    /// Create a configuration for 32-bit x86.
    pub fn x86() -> Self {
        Self {
            ptr_size: 32,
            sp_name: "esp".to_string(),
            fp_name: "ebp".to_string(),
            arg_regs: vec![],
            ret_regs: vec!["eax".to_string(), "xmm0".to_string(), "st0".to_string()],
            caller_saved_regs: ["eax", "ecx", "edx"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ..Default::default()
        }
    }

    /// Create a configuration for 64-bit x86.
    pub fn x86_64() -> Self {
        Self::default()
    }

    /// Create a configuration for ARM.
    pub fn arm() -> Self {
        Self {
            ptr_size: 32,
            sp_name: "sp".to_string(),
            fp_name: "fp".to_string(),
            arg_regs: ["r0", "r1", "r2", "r3"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ret_regs: vec!["r0".to_string()],
            caller_saved_regs: ["r0", "r1", "r2", "r3", "r12", "lr", "ip"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ..Default::default()
        }
    }

    /// Create a configuration for AArch64.
    pub fn aarch64() -> Self {
        Self {
            ptr_size: 64,
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ret_regs: vec!["x0".to_string(), "w0".to_string()],
            caller_saved_regs: [
                "x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12",
                "x13", "x14", "x15", "x16", "x17",
            ]
            .into_iter()
            .map(str::to_string)
            .collect(),
            ..Default::default()
        }
    }

    /// Create a configuration for RISC-V RV32.
    pub fn riscv32() -> Self {
        Self {
            ptr_size: 32,
            sp_name: "sp".to_string(),
            fp_name: "s0".to_string(),
            arg_regs: ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ret_regs: vec!["a0".to_string()],
            caller_saved_regs: [
                "ra", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "a0", "a1", "a2", "a3", "a4", "a5",
                "a6", "a7",
            ]
            .into_iter()
            .map(str::to_string)
            .collect(),
            ..Default::default()
        }
    }

    /// Create a configuration for RISC-V RV64.
    pub fn riscv64() -> Self {
        Self {
            ptr_size: 64,
            sp_name: "sp".to_string(),
            fp_name: "s0".to_string(),
            arg_regs: ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ret_regs: vec!["a0".to_string()],
            caller_saved_regs: [
                "ra", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "a0", "a1", "a2", "a3", "a4", "a5",
                "a6", "a7",
            ]
            .into_iter()
            .map(str::to_string)
            .collect(),
            ..Default::default()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalStructFieldAccess {
    pub arg_index: usize,
    pub field_offset: u64,
    pub access_size: u32,
    pub is_write: bool,
}

#[derive(Debug, Clone, Default)]
pub struct DecompilerContext {
    /// Function address to name mapping.
    pub function_names: std::collections::HashMap<u64, String>,
    /// String literal addresses.
    pub strings: std::collections::HashMap<u64, String>,
    /// Symbol/global variable names.
    pub symbols: std::collections::HashMap<u64, String>,
    /// Externally recovered type and layout facts.
    pub type_facts: FunctionTypeFacts,
}

impl DecompilerContext {
    pub fn with_function_names(
        mut self,
        function_names: std::collections::HashMap<u64, String>,
    ) -> Self {
        self.function_names = function_names;
        self
    }

    pub fn with_strings(mut self, strings: std::collections::HashMap<u64, String>) -> Self {
        self.strings = strings;
        self
    }

    pub fn with_symbols(mut self, symbols: std::collections::HashMap<u64, String>) -> Self {
        self.symbols = symbols;
        self
    }

    pub fn with_type_facts(mut self, type_facts: FunctionTypeFacts) -> Self {
        self.type_facts = type_facts.canonicalized();
        self
    }
}

#[derive(Debug, Clone)]
pub struct DecompilerInput {
    pub prepared_ssa: r2ssa::PreparedFunctionSSA,
    pub interproc_summary_set: Option<r2ssa::InterprocSummarySet>,
    pub context: DecompilerContext,
}

impl DecompilerInput {
    pub fn new(prepared_ssa: r2ssa::PreparedFunctionSSA, mut context: DecompilerContext) -> Self {
        context.type_facts = context.type_facts.canonicalized();
        Self {
            prepared_ssa,
            interproc_summary_set: None,
            context,
        }
    }

    pub fn with_context(mut self, mut context: DecompilerContext) -> Self {
        context.type_facts = context.type_facts.canonicalized();
        self.context = context;
        self
    }

    pub fn with_interproc_summary_set(
        mut self,
        interproc_summary_set: Option<r2ssa::InterprocSummarySet>,
    ) -> Self {
        self.interproc_summary_set = interproc_summary_set;
        self
    }
}

/// The main decompiler.
pub struct Decompiler {
    config: DecompilerConfig,
    context: DecompilerContext,
}

impl Decompiler {
    /// Create a new decompiler with the given configuration.
    pub fn new(config: DecompilerConfig) -> Self {
        Self {
            config,
            context: DecompilerContext::default(),
        }
    }

    /// Set external context (function names, strings, symbols).
    pub fn with_context(mut self, mut context: DecompilerContext) -> Self {
        context.type_facts = context.type_facts.canonicalized();
        self.context = context;
        self
    }

    /// Set function names for call target resolution.
    pub fn set_function_names(&mut self, names: std::collections::HashMap<u64, String>) {
        self.context.function_names = names;
    }

    /// Set string literals for address resolution.
    pub fn set_strings(&mut self, strings: std::collections::HashMap<u64, String>) {
        self.context.strings = strings;
    }

    /// Set symbol names for global variable resolution.
    pub fn set_symbols(&mut self, symbols: std::collections::HashMap<u64, String>) {
        self.context.symbols = symbols;
    }

    /// Set externally recovered known function signatures keyed by name.
    pub fn set_known_function_signatures<T>(
        &mut self,
        signatures: std::collections::HashMap<String, T>,
    ) where
        T: Into<FunctionType>,
    {
        self.context.type_facts.known_function_signatures = signatures
            .into_iter()
            .map(|(name, sig)| (name, sig.into()))
            .collect();
    }

    /// Set externally recovered host type database.
    pub fn set_external_type_db(&mut self, external_type_db: ExternalTypeDb) {
        self.context.type_facts.external_type_db = external_type_db;
    }

    /// Set externally recovered type facts.
    pub fn set_type_facts(&mut self, type_facts: FunctionTypeFacts) {
        self.context.type_facts = type_facts.canonicalized();
    }

    /// Decompile an SSA function to C code.
    pub fn decompile(&self, func: &SSAFunction) -> String {
        // Build the C function
        let c_func = self.build_function(func);

        // Generate code
        let mut codegen = CodeGenerator::new(self.config.codegen.clone());
        codegen.generate_function(&c_func)
    }

    /// Decompile a prepared function with an explicit typed context payload.
    pub fn decompile_input(&self, input: &DecompilerInput) -> String {
        let c_func = self.build_function_from_input(input);
        let mut codegen = CodeGenerator::new(self.config.codegen.clone());
        codegen.generate_function(&c_func)
    }

    /// Build a C function from a prepared function + typed context payload.
    pub fn build_function_from_input(&self, input: &DecompilerInput) -> CFunction {
        let decompiler = Self::new(self.config.clone()).with_context(input.context.clone());
        decompiler.build_function_internal(
            input.prepared_ssa.function(),
            Some(&input.prepared_ssa),
            input.interproc_summary_set.as_ref(),
        )
    }

    fn stmt_has_content(stmt: &CStmt) -> bool {
        match stmt {
            CStmt::Empty => false,
            CStmt::Block(stmts) => !stmts.is_empty(),
            _ => true,
        }
    }

    fn prepend_comment(stmt: CStmt, text: String) -> CStmt {
        let comment = CStmt::comment(text);
        match stmt {
            CStmt::Empty => CStmt::Block(vec![comment]),
            CStmt::Block(mut stmts) => {
                stmts.insert(0, comment);
                CStmt::Block(stmts)
            }
            other => CStmt::Block(vec![comment, other]),
        }
    }

    fn linearize_function_body(
        &self,
        func: &SSAFunction,
        fold_ctx: &FoldingContext<'_>,
    ) -> Vec<CStmt> {
        let blocks: Vec<_> = func.blocks().cloned().collect();
        let mut stmts = Vec::new();

        for block in &blocks {
            for stmt in fold_ctx.fold_block(block, block.addr) {
                if !matches!(stmt, CStmt::Empty) {
                    stmts.push(stmt);
                }
            }
        }

        stmts
    }

    /// Build a C function from an SSA function.
    pub fn build_function(&self, func: &SSAFunction) -> CFunction {
        self.build_function_internal(func, None, None)
    }

    fn build_function_internal(
        &self,
        func: &SSAFunction,
        prepared: Option<&r2ssa::PreparedFunctionSSA>,
        interproc_summary_set: Option<&r2ssa::InterprocSummarySet>,
    ) -> CFunction {
        // Materialize phis on non-critical edges to reduce SSA artifacts in output.
        let normalized_func = normalize::materialize_phis(func);
        let func = &normalized_func;

        // Recover variables
        let mut var_recovery = VariableRecovery::new_with_abi(
            &self.config.sp_name,
            &self.config.fp_name,
            self.config.ptr_size,
            self.config.arg_regs.clone(),
            self.config.ret_regs.clone(),
        );
        var_recovery.set_type_facts(self.context.type_facts.clone());
        var_recovery.recover(func);

        let skip_runtime_type_inference = should_skip_runtime_type_inference(prepared);
        let type_inference = (!skip_runtime_type_inference).then(|| {
            let mut type_inference = TypeInference::new_with_abi(
                self.config.ptr_size,
                self.config.arg_regs.clone(),
                self.config.ret_regs.clone(),
            );
            if !self.context.function_names.is_empty() {
                type_inference.set_function_names(self.context.function_names.clone());
            }
            type_inference.set_external_signature(self.context.type_facts.merged_signature.clone());
            for (name, signature) in &self.context.type_facts.known_function_signatures {
                type_inference.add_function_type(name, signature.clone());
            }
            type_inference.set_external_stack_slots(self.context.type_facts.stack_slots.clone());
            if !self.context.type_facts.external_type_db.structs.is_empty()
                || !self.context.type_facts.external_type_db.unions.is_empty()
                || !self.context.type_facts.external_type_db.enums.is_empty()
            {
                type_inference
                    .set_external_type_db(self.context.type_facts.external_type_db.clone());
            }
            if let Some(prepared) = prepared {
                type_inference.set_prepared_ssa(prepared);
            } else {
                type_inference.set_decompile_prep_facts(func.decompile_prep_facts());
            }
            type_inference.infer_function(func);
            type_inference
        });
        let mut type_hints = if let Some(type_inference) = type_inference.as_ref() {
            type_inference
                .var_type_hints()
                .into_iter()
                .map(|(name, ty)| (name, type_like_to_ctype(&ty)))
                .collect::<std::collections::HashMap<_, _>>()
        } else {
            seed_runtime_type_hints_from_facts_and_recovery(&self.context.type_facts, &var_recovery)
        };
        let combined_type_oracle = type_inference
            .as_ref()
            .and_then(TypeInference::combined_type_oracle);
        let type_oracle = combined_type_oracle
            .as_ref()
            .map(|oracle| oracle as &dyn TypeOracle);

        let known_function_signatures = self
            .context
            .type_facts
            .known_function_signatures
            .iter()
            .map(|(name, ty)| (normalize_callee_name(name), ty.clone()))
            .collect::<std::collections::HashMap<_, _>>();

        let recovered_param_infos: Vec<_> = var_recovery
            .parameters()
            .iter()
            .map(|v| {
                (
                    v.ssa_var.clone(),
                    ast::CParam {
                        ty: type_inference
                            .as_ref()
                            .map(|type_inference| {
                                type_like_to_ctype(&type_inference.get_type(&v.ssa_var))
                            })
                            .unwrap_or_else(|| v.ty.clone()),
                        name: v.name.clone(),
                    },
                )
            })
            .collect();
        let params = merge_params_with_external_signature(
            recovered_param_infos
                .iter()
                .map(|(_, param)| param.clone())
                .collect(),
            self.context.type_facts.merged_signature.as_ref(),
        );
        let param_register_aliases = build_param_register_aliases(
            &params,
            &recovered_param_infos,
            &self.context.type_facts.register_params,
            &self.config.arg_regs,
        );
        for (idx, (_ssa_var, _)) in recovered_param_infos.iter().enumerate() {
            let Some(param) = params.get(idx) else {
                continue;
            };
            let param_ty = param.ty.clone();
            type_hints.insert(param.name.clone(), param_ty.clone());
            type_hints.insert(param.name.to_ascii_lowercase(), param_ty);
        }
        for (reg_alias, param_name) in &param_register_aliases {
            let Some(param) = params.iter().find(|param| param.name == *param_name) else {
                continue;
            };
            type_hints
                .entry(reg_alias.clone())
                .or_insert_with(|| param.ty.clone());
            type_hints
                .entry(reg_alias.to_ascii_lowercase())
                .or_insert_with(|| param.ty.clone());
        }
        let inferred_ret_type = type_inference
            .as_ref()
            .map(|type_inference| self.infer_return_type(func, type_inference))
            .or_else(|| {
                self.context
                    .type_facts
                    .merged_signature
                    .as_ref()
                    .and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype))
            })
            .unwrap_or(CType::Unknown);
        let signature_ret_type = self
            .context
            .type_facts
            .merged_signature
            .as_ref()
            .and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype));

        let fold_arch = FoldArchConfig {
            ptr_size: self.config.ptr_size,
            sp_name: self.config.sp_name.clone(),
            fp_name: self.config.fp_name.clone(),
            ret_reg_name: self
                .config
                .ret_regs
                .first()
                .cloned()
                .unwrap_or_else(|| "rax".to_string()),
            arg_regs: self.config.arg_regs.clone(),
            caller_saved_regs: self.config.caller_saved_regs.clone(),
        };
        let prepared_semantic_view = should_use_prepared_semantic_view(prepared).then(|| {
            analysis::PreparedSemanticView::build(analysis::PreparedSemanticViewInputs {
                prepared: prepared.expect("prepared semantic view requires prepared artifact"),
                interproc_summary_set,
                abi_arg_regs: &self.config.arg_regs,
                ret_reg_name: &fold_arch.ret_reg_name,
                function_names: &self.context.function_names,
                symbols: &self.context.symbols,
                callee_facts: &self.context.type_facts.callee_facts,
                stack_slots: &self.context.type_facts.stack_slots,
                visible_bindings: &self.context.type_facts.visible_bindings,
                param_register_aliases: &param_register_aliases,
            })
        });
        let fold_inputs = FoldInputs {
            arch: &fold_arch,
            function_names: &self.context.function_names,
            strings: &self.context.strings,
            symbols: &self.context.symbols,
            known_function_signatures: &known_function_signatures,
            callee_facts: &self.context.type_facts.callee_facts,
            stack_slots: &self.context.type_facts.stack_slots,
            #[cfg(test)]
            external_stack_vars: &self.context.type_facts.external_stack_vars,
            visible_bindings: &self.context.type_facts.visible_bindings,
            external_type_db: &self.context.type_facts.external_type_db,
            param_register_aliases: &param_register_aliases,
            type_hints: &type_hints,
            type_oracle,
            function_return_type: signature_ret_type.as_ref().or(Some(&inferred_ret_type)),
            prepared_ssa: prepared,
            interproc_summary_set,
            prepared_semantic_view: prepared_semantic_view.as_ref(),
            prepared_objects: prepared.map(|artifact| artifact.objects()),
            prepared_memory: prepared.map(|artifact| artifact.memory()),
            prepared_predicates: prepared.map(|artifact| artifact.predicates()),
            prepared_call_sites: prepared.map(|artifact| artifact.call_sites()),
        };
        let mut fold_ctx = FoldingContext::from_inputs(fold_inputs);
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        fold_ctx.analyze_blocks(&fold_blocks);
        fold_ctx.analyze_function_structure(func);

        // Structure control flow (primary path: folded)
        let mut structurer = ControlFlowStructurer::new(func, &fold_ctx);

        // Get set of variables that survive folding before structuring.
        let emitted_vars = structurer.emitted_var_names();
        let mut use_conservative_locals = false;
        let mut is_linear_fallback = false;

        let folded_stmt = structurer.structure();
        let mut body_stmt = folded_stmt;

        if !Self::stmt_has_content(&body_stmt) {
            let folded_reason = structurer
                .safety_reason()
                .map(str::to_string)
                .unwrap_or_else(|| "folded structuring produced empty output".to_string());

            // Fallback 1: unfolded structuring
            let mut unfolded = ControlFlowStructurer::new_unfolded(func, &fold_ctx);
            let unfolded_stmt = unfolded.structure();

            if Self::stmt_has_content(&unfolded_stmt) {
                use_conservative_locals = true;
                body_stmt = Self::prepend_comment(
                    unfolded_stmt,
                    format!("r2dec fallback: {}", folded_reason),
                );
            } else {
                let unfolded_reason = unfolded
                    .safety_reason()
                    .map(str::to_string)
                    .unwrap_or_else(|| "unfolded structuring produced empty output".to_string());

                // Fallback 2: linear block emission
                let mut linear_stmts = self.linearize_function_body(func, &fold_ctx);
                let fallback_reason = format!("{}; {}", folded_reason, unfolded_reason);

                use_conservative_locals = true;
                is_linear_fallback = true;
                if linear_stmts.is_empty() {
                    body_stmt = CStmt::Block(vec![CStmt::comment(format!(
                        "r2dec fallback: {} -> no statements recovered",
                        fallback_reason
                    ))]);
                } else {
                    linear_stmts.insert(
                        0,
                        CStmt::comment(format!(
                            "r2dec fallback: {} -> linear block emission",
                            fallback_reason
                        )),
                    );
                    body_stmt = CStmt::Block(linear_stmts);
                }
            }
        }

        body_stmt = fold_ctx.normalize_final_stmt_calls(body_stmt);
        body_stmt = fold_ctx.prune_dead_temp_assignments_in_stmt(body_stmt);

        // Build the C function
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));

        // Convert body to statements
        let body = self.stmt_to_vec(body_stmt);
        let body_visible_names = collect_stmt_var_names(&body);
        let param_name_set = params
            .iter()
            .map(|param| param.name.to_ascii_lowercase())
            .collect::<HashSet<_>>();
        let param_home_offsets = fold_ctx
            .stack_arg_aliases_map()
            .iter()
            .filter_map(|(offset, alias)| {
                param_name_set
                    .contains(&alias.to_ascii_lowercase())
                    .then_some(*offset)
            })
            .chain(
                self.context
                    .type_facts
                    .visible_bindings
                    .iter()
                    .filter_map(|binding| {
                        matches!(binding.kind, VisibleBindingKind::HiddenHome)
                            .then(|| binding.stack_slot.as_ref().map(|slot| slot.offset))
                            .flatten()
                    }),
            )
            .collect::<HashSet<_>>();
        let body_visible_stack_offsets = collect_visible_stack_offsets(
            &body_visible_names,
            &self.context.type_facts.visible_bindings,
            &self.context.type_facts.stack_slots,
            &param_name_set,
        );

        // Collect locals -- on fallback keep locals conservatively.
        let locals: Vec<ast::CLocal> = if use_conservative_locals {
            var_recovery
                .locals()
                .iter()
                .filter(|v| {
                    !v.stack_offset
                        .is_some_and(|offset| param_home_offsets.contains(&offset))
                })
                .map(|v| ast::CLocal {
                    ty: type_inference
                        .as_ref()
                        .map(|type_inference| {
                            type_like_to_ctype(&type_inference.get_type(&v.ssa_var))
                        })
                        .unwrap_or_else(|| v.ty.clone()),
                    name: v.name.clone(),
                    stack_offset: v.stack_offset,
                })
                .collect()
        } else {
            let mut selected = var_recovery
                .locals()
                .iter()
                .filter(|v| {
                    !v.stack_offset
                        .is_some_and(|offset| param_home_offsets.contains(&offset))
                        && (emitted_vars.contains(&v.name)
                            || body_visible_names.contains(&v.name)
                            || v.stack_offset
                                .is_some_and(|offset| body_visible_stack_offsets.contains(&offset)))
                })
                .map(|v| ast::CLocal {
                    ty: type_inference
                        .as_ref()
                        .map(|type_inference| {
                            type_like_to_ctype(&type_inference.get_type(&v.ssa_var))
                        })
                        .unwrap_or_else(|| v.ty.clone()),
                    name: v.name.clone(),
                    stack_offset: v.stack_offset,
                })
                .collect::<Vec<_>>();
            let mut seen_offsets = HashSet::new();
            selected.retain(|local| match local.stack_offset {
                Some(offset) => seen_offsets.insert(offset),
                None => true,
            });
            selected
        };

        let mut c_function = CFunction {
            name: func_name,
            ret_type: self
                .context
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype))
                .unwrap_or_else(|| inferred_ret_type.clone()),
            params,
            locals,
            body,
        };

        // Apply post-structuring suffix cleanup for folded/unfolded paths.
        // Linear fallback intentionally keeps its raw expression-builder output.
        if !is_linear_fallback {
            let mut known_function_names = HashSet::new();
            for name in self.context.function_names.values() {
                known_function_names.insert(name.to_ascii_lowercase());
            }
            for name in self.context.type_facts.known_function_signatures.keys() {
                known_function_names.insert(name.to_ascii_lowercase());
            }
            post_rename::rewrite_function_identifiers(&mut c_function, &known_function_names);
        }
        rewrite_reserved_param_stack_home_uses(
            &mut c_function,
            fold_ctx.stack_arg_aliases_map(),
            fold_ctx.stack_vars_map(),
            fold_ctx.inputs.visible_bindings,
            fold_ctx.inputs.stack_slots,
        );
        prune_unused_pure_locals(&mut c_function);

        c_function
    }

    /// Convert a CStmt to a Vec<CStmt>.
    fn stmt_to_vec(&self, stmt: CStmt) -> Vec<CStmt> {
        match stmt {
            CStmt::Block(stmts) => stmts,
            CStmt::Empty => vec![],
            other => vec![other],
        }
    }

    fn infer_return_type(&self, func: &SSAFunction, type_inference: &TypeInference) -> CType {
        let mut candidates = Vec::new();

        for block in func.blocks() {
            for op in &block.ops {
                let SSAOp::Return { target } = op else {
                    continue;
                };

                let target_name = target.name.to_ascii_lowercase();
                if target_name.starts_with("xmm0") || target_name.starts_with("st0") {
                    let bits = if target.size.saturating_mul(8) <= 32 {
                        32
                    } else {
                        64
                    };
                    candidates.push(CType::Float(bits));
                    continue;
                }

                candidates.push(type_like_to_ctype(&type_inference.get_type(target)));
            }
        }

        if candidates.is_empty() {
            return CType::Void;
        }

        let mut meaningful: Vec<CType> = candidates
            .into_iter()
            .filter(|ty| !matches!(ty, CType::Unknown))
            .collect();
        if meaningful.is_empty() {
            return CType::Int(32);
        }
        if meaningful.iter().all(|ty| ty == &meaningful[0]) {
            return meaningful.remove(0);
        }
        if let Some(float_ty) = meaningful
            .iter()
            .find(|ty| matches!(ty, CType::Float(_)))
            .cloned()
        {
            return float_ty;
        }
        meaningful.remove(0)
    }
}

fn collect_expr_var_names(expr: &CExpr, out: &mut HashSet<String>) {
    match expr {
        CExpr::Var(name) => {
            out.insert(name.clone());
        }
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Paren(operand)
        | CExpr::AddrOf(operand)
        | CExpr::Deref(operand) => collect_expr_var_names(operand, out),
        CExpr::Comma(items) => {
            for item in items {
                collect_expr_var_names(item, out);
            }
        }
        CExpr::Binary { left, right, .. } => {
            collect_expr_var_names(left, out);
            collect_expr_var_names(right, out);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_expr_var_names(cond, out);
            collect_expr_var_names(then_expr, out);
            collect_expr_var_names(else_expr, out);
        }
        CExpr::Call { func, args } => {
            collect_expr_var_names(func, out);
            for arg in args {
                collect_expr_var_names(arg, out);
            }
        }
        CExpr::Subscript { base, index } => {
            collect_expr_var_names(base, out);
            collect_expr_var_names(index, out);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            collect_expr_var_names(base, out);
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::CharLit(_)
        | CExpr::StringLit(_)
        | CExpr::Sizeof(_)
        | CExpr::SizeofType(_) => {}
    }
}

fn collect_stmt_var_names(stmts: &[CStmt]) -> HashSet<String> {
    fn visit_stmt(stmt: &CStmt, out: &mut HashSet<String>) {
        match stmt {
            CStmt::Empty
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Comment(_)
            | CStmt::Goto(_)
            | CStmt::Label(_) => {}
            CStmt::Expr(expr) => collect_expr_var_names(expr, out),
            CStmt::Return(expr) => {
                if let Some(expr) = expr {
                    collect_expr_var_names(expr, out);
                }
            }
            CStmt::Decl { init, .. } => {
                if let Some(init) = init {
                    collect_expr_var_names(init, out);
                }
            }
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    visit_stmt(stmt, out);
                }
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                collect_expr_var_names(cond, out);
                visit_stmt(then_body, out);
                if let Some(else_body) = else_body {
                    visit_stmt(else_body, out);
                }
            }
            CStmt::While { cond, body } => {
                collect_expr_var_names(cond, out);
                visit_stmt(body, out);
            }
            CStmt::DoWhile { body, cond } => {
                visit_stmt(body, out);
                collect_expr_var_names(cond, out);
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                if let Some(init) = init {
                    visit_stmt(init, out);
                }
                if let Some(cond) = cond {
                    collect_expr_var_names(cond, out);
                }
                if let Some(update) = update {
                    collect_expr_var_names(update, out);
                }
                visit_stmt(body, out);
            }
            CStmt::Switch {
                expr,
                cases,
                default,
            } => {
                collect_expr_var_names(expr, out);
                for case in cases {
                    collect_expr_var_names(&case.value, out);
                    for stmt in &case.body {
                        visit_stmt(stmt, out);
                    }
                }
                if let Some(default) = default {
                    for stmt in default {
                        visit_stmt(stmt, out);
                    }
                }
            }
        }
    }

    let mut names = HashSet::new();
    for stmt in stmts {
        visit_stmt(stmt, &mut names);
    }
    names
}

fn parse_visible_stack_offset(
    name: &str,
    visible_bindings: &[VisibleBinding],
    stack_slots: &std::collections::BTreeMap<StackSlotKey, r2types::ExternalStackSlotSpec>,
    param_names: &HashSet<String>,
) -> Option<i64> {
    let lower = name.trim().to_ascii_lowercase();
    if param_names.contains(&lower) {
        return None;
    }
    if lower == "saved_fp" {
        return Some(0);
    }
    if let Some(rest) = lower.strip_prefix("stack_") {
        return i64::from_str_radix(rest, 16).ok();
    }
    if let Some(rest) = lower.strip_prefix("local_") {
        return i64::from_str_radix(rest, 16).ok().map(|v| -v);
    }
    if let Some(rest) = lower.strip_prefix("arg_") {
        return i64::from_str_radix(rest, 16).ok().map(|v| -v);
    }
    if let Some(rest) = lower.strip_prefix("var_") {
        let trimmed = rest.strip_suffix('h').unwrap_or(rest);
        if !trimmed.is_empty() && trimmed.chars().all(|ch| ch.is_ascii_hexdigit()) {
            return i64::from_str_radix(trimmed, 16).ok().map(|v| -v);
        }
    }
    visible_bindings
        .iter()
        .find(|binding| binding.name.eq_ignore_ascii_case(name))
        .and_then(|binding| binding.stack_slot.as_ref().map(|slot| slot.offset))
        .or_else(|| {
            stack_slots
                .iter()
                .find(|(_, slot_spec)| slot_spec.name.eq_ignore_ascii_case(name))
                .map(|(slot_key, _)| slot_key.offset)
        })
}

fn collect_visible_stack_offsets(
    names: &HashSet<String>,
    visible_bindings: &[VisibleBinding],
    stack_slots: &std::collections::BTreeMap<StackSlotKey, r2types::ExternalStackSlotSpec>,
    param_names: &HashSet<String>,
) -> HashSet<i64> {
    names
        .iter()
        .filter_map(|name| {
            parse_visible_stack_offset(name, visible_bindings, stack_slots, param_names)
        })
        .collect()
}

fn generic_stack_home_name_for_offset(offset: i64) -> String {
    if offset < 0 {
        format!("local_{:x}", (-offset) as u64)
    } else {
        format!("stack_{:x}", offset as u64)
    }
}

fn is_low_quality_stack_home_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower == "saved_fp"
        || lower.starts_with("local_")
        || lower.starts_with("stack_")
        || lower.starts_with("arg_")
        || lower.starts_with("var_")
}

fn stack_slot_matches_rewrite_offset(slot: &StackSlotKey, offset: i64) -> bool {
    if slot.offset == offset {
        return true;
    }
    matches!(slot.base, r2types::ExternalStackBase::FramePointer) && -slot.offset == offset
}

fn rewrite_reserved_param_stack_home_uses(
    func: &mut CFunction,
    stack_arg_aliases: &std::collections::HashMap<i64, String>,
    stack_vars: &std::collections::HashMap<i64, String>,
    visible_bindings: &[VisibleBinding],
    stack_slots: &std::collections::BTreeMap<StackSlotKey, r2types::ExternalStackSlotSpec>,
) {
    let param_names = func
        .params
        .iter()
        .map(|param| param.name.to_ascii_lowercase())
        .collect::<HashSet<_>>();
    let mut rename_map = std::collections::HashMap::new();
    for (offset, alias) in stack_arg_aliases {
        let target = alias.trim();
        if target.is_empty() || !param_names.contains(&target.to_ascii_lowercase()) {
            continue;
        }

        rename_map.insert(
            generic_stack_home_name_for_offset(*offset),
            target.to_string(),
        );

        if let Some(stack_name) = stack_vars.get(offset)
            && is_low_quality_stack_home_name(stack_name)
        {
            rename_map.insert(stack_name.to_ascii_lowercase(), target.to_string());
        }

        for binding in visible_bindings {
            if !binding
                .stack_slot
                .as_ref()
                .is_some_and(|slot| stack_slot_matches_rewrite_offset(slot, *offset))
            {
                continue;
            }
            let name = binding.name.trim();
            if !name.is_empty() && is_low_quality_stack_home_name(name) {
                rename_map.insert(name.to_ascii_lowercase(), target.to_string());
            }
        }

        for (slot_key, slot_spec) in stack_slots {
            if !stack_slot_matches_rewrite_offset(slot_key, *offset) {
                continue;
            }
            let name = slot_spec.name.trim();
            if !name.is_empty() && is_low_quality_stack_home_name(name) {
                rename_map.insert(name.to_ascii_lowercase(), target.to_string());
            }
        }
    }

    if rename_map.is_empty() {
        return;
    }

    func.locals
        .retain(|local| !rename_map.contains_key(&local.name.to_ascii_lowercase()));
    for stmt in &mut func.body {
        rewrite_stmt_reserved_param_stack_homes(stmt, &rename_map);
    }
}

fn rewrite_stmt_reserved_param_stack_homes(
    stmt: &mut CStmt,
    rename_map: &std::collections::HashMap<String, String>,
) {
    match stmt {
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
        CStmt::Expr(expr) => rewrite_expr_reserved_param_stack_homes(expr, rename_map, true),
        CStmt::Decl { init, .. } => {
            if let Some(init) = init {
                rewrite_expr_reserved_param_stack_homes(init, rename_map, true);
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                rewrite_stmt_reserved_param_stack_homes(stmt, rename_map);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            rewrite_expr_reserved_param_stack_homes(cond, rename_map, true);
            rewrite_stmt_reserved_param_stack_homes(then_body, rename_map);
            if let Some(else_body) = else_body {
                rewrite_stmt_reserved_param_stack_homes(else_body, rename_map);
            }
        }
        CStmt::While { cond, body } => {
            rewrite_expr_reserved_param_stack_homes(cond, rename_map, true);
            rewrite_stmt_reserved_param_stack_homes(body, rename_map);
        }
        CStmt::DoWhile { body, cond } => {
            rewrite_stmt_reserved_param_stack_homes(body, rename_map);
            rewrite_expr_reserved_param_stack_homes(cond, rename_map, true);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                rewrite_stmt_reserved_param_stack_homes(init, rename_map);
            }
            if let Some(cond) = cond {
                rewrite_expr_reserved_param_stack_homes(cond, rename_map, true);
            }
            if let Some(update) = update {
                rewrite_expr_reserved_param_stack_homes(update, rename_map, true);
            }
            rewrite_stmt_reserved_param_stack_homes(body, rename_map);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            rewrite_expr_reserved_param_stack_homes(expr, rename_map, true);
            for case in cases {
                rewrite_expr_reserved_param_stack_homes(&mut case.value, rename_map, true);
                for stmt in &mut case.body {
                    rewrite_stmt_reserved_param_stack_homes(stmt, rename_map);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    rewrite_stmt_reserved_param_stack_homes(stmt, rename_map);
                }
            }
        }
        CStmt::Return(expr) => {
            if let Some(expr) = expr {
                rewrite_expr_reserved_param_stack_homes(expr, rename_map, true);
            }
        }
    }
}

fn rewrite_expr_reserved_param_stack_homes(
    expr: &mut CExpr,
    rename_map: &std::collections::HashMap<String, String>,
    allow_plain_var_rewrite: bool,
) {
    match expr {
        CExpr::Var(name) if allow_plain_var_rewrite => {
            if let Some(target) = rename_map.get(&name.to_ascii_lowercase()) {
                *name = target.clone();
            }
        }
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Paren(operand)
        | CExpr::Sizeof(operand) => {
            rewrite_expr_reserved_param_stack_homes(operand, rename_map, allow_plain_var_rewrite);
        }
        CExpr::AddrOf(operand) => {
            rewrite_expr_reserved_param_stack_homes(operand, rename_map, false);
        }
        CExpr::Deref(operand) => {
            if let Some(target) = reserved_param_stack_home_target_name(operand, rename_map) {
                *expr = CExpr::Var(target);
                return;
            }
            rewrite_expr_reserved_param_stack_homes(operand, rename_map, false);
        }
        CExpr::Binary { left, right, .. } => {
            rewrite_expr_reserved_param_stack_homes(left, rename_map, allow_plain_var_rewrite);
            rewrite_expr_reserved_param_stack_homes(right, rename_map, allow_plain_var_rewrite);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            rewrite_expr_reserved_param_stack_homes(cond, rename_map, allow_plain_var_rewrite);
            rewrite_expr_reserved_param_stack_homes(then_expr, rename_map, allow_plain_var_rewrite);
            rewrite_expr_reserved_param_stack_homes(else_expr, rename_map, allow_plain_var_rewrite);
        }
        CExpr::Call { func, args } => {
            rewrite_expr_reserved_param_stack_homes(func, rename_map, allow_plain_var_rewrite);
            for arg in args {
                rewrite_expr_reserved_param_stack_homes(arg, rename_map, allow_plain_var_rewrite);
            }
        }
        CExpr::Subscript { base, index } => {
            rewrite_expr_reserved_param_stack_homes(base, rename_map, allow_plain_var_rewrite);
            rewrite_expr_reserved_param_stack_homes(index, rename_map, allow_plain_var_rewrite);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            rewrite_expr_reserved_param_stack_homes(base, rename_map, allow_plain_var_rewrite);
        }
        CExpr::Comma(items) => {
            for item in items {
                rewrite_expr_reserved_param_stack_homes(item, rename_map, allow_plain_var_rewrite);
            }
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::SizeofType(_)
        | CExpr::Var(_) => {}
    }
}

fn reserved_param_stack_home_target_name(
    expr: &CExpr,
    rename_map: &std::collections::HashMap<String, String>,
) -> Option<String> {
    match expr {
        CExpr::Var(name) => rename_map.get(&name.to_ascii_lowercase()).cloned(),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
            reserved_param_stack_home_target_name(inner, rename_map)
        }
        _ => None,
    }
}

fn prune_unused_pure_locals(func: &mut CFunction) {
    loop {
        let live_reads = collect_function_local_reads(func);
        let dead_locals = func
            .locals
            .iter()
            .map(|local| local.name.to_ascii_lowercase())
            .filter(|name| !live_reads.contains(name))
            .collect::<HashSet<_>>();

        if dead_locals.is_empty() {
            break;
        }

        func.locals
            .retain(|local| !dead_locals.contains(&local.name.to_ascii_lowercase()));
        prune_unused_pure_local_stmts(&mut func.body, &dead_locals);
    }
}

fn collect_function_local_reads(func: &CFunction) -> HashSet<String> {
    let mut reads = HashSet::new();
    for stmt in &func.body {
        collect_stmt_local_reads(stmt, &mut reads);
    }
    reads
}

fn collect_stmt_local_reads(stmt: &CStmt, reads: &mut HashSet<String>) {
    match stmt {
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
        CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) => {
            if !matches!(left.as_ref(), CExpr::Var(_)) {
                collect_expr_local_reads(left, reads);
            }
            collect_expr_local_reads(right, reads);
        }
        CStmt::Expr(expr) => collect_expr_local_reads(expr, reads),
        CStmt::Decl { init, .. } => {
            if let Some(init) = init {
                collect_expr_local_reads(init, reads);
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                collect_stmt_local_reads(stmt, reads);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            collect_expr_local_reads(cond, reads);
            collect_stmt_local_reads(then_body, reads);
            if let Some(else_body) = else_body {
                collect_stmt_local_reads(else_body, reads);
            }
        }
        CStmt::While { cond, body } => {
            collect_expr_local_reads(cond, reads);
            collect_stmt_local_reads(body, reads);
        }
        CStmt::DoWhile { body, cond } => {
            collect_stmt_local_reads(body, reads);
            collect_expr_local_reads(cond, reads);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                collect_stmt_local_reads(init, reads);
            }
            if let Some(cond) = cond {
                collect_expr_local_reads(cond, reads);
            }
            if let Some(update) = update {
                collect_expr_local_reads(update, reads);
            }
            collect_stmt_local_reads(body, reads);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            collect_expr_local_reads(expr, reads);
            for case in cases {
                collect_expr_local_reads(&case.value, reads);
                for stmt in &case.body {
                    collect_stmt_local_reads(stmt, reads);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    collect_stmt_local_reads(stmt, reads);
                }
            }
        }
        CStmt::Return(Some(expr)) => collect_expr_local_reads(expr, reads),
        CStmt::Return(None) => {}
    }
}

fn collect_expr_local_reads(expr: &CExpr, reads: &mut HashSet<String>) {
    match expr {
        CExpr::Var(name) => {
            reads.insert(name.to_ascii_lowercase());
        }
        CExpr::Paren(inner)
        | CExpr::AddrOf(inner)
        | CExpr::Deref(inner)
        | CExpr::Cast { expr: inner, .. }
        | CExpr::Unary { operand: inner, .. }
        | CExpr::Sizeof(inner) => collect_expr_local_reads(inner, reads),
        CExpr::Binary { left, right, .. } => {
            collect_expr_local_reads(left, reads);
            collect_expr_local_reads(right, reads);
        }
        CExpr::Subscript { base, index } => {
            collect_expr_local_reads(base, reads);
            collect_expr_local_reads(index, reads);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            collect_expr_local_reads(base, reads);
        }
        CExpr::Call { func, args } => {
            collect_expr_local_reads(func, reads);
            for arg in args {
                collect_expr_local_reads(arg, reads);
            }
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_expr_local_reads(cond, reads);
            collect_expr_local_reads(then_expr, reads);
            collect_expr_local_reads(else_expr, reads);
        }
        CExpr::Comma(items) => {
            for item in items {
                collect_expr_local_reads(item, reads);
            }
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::SizeofType(_) => {}
    }
}

fn prune_unused_pure_local_stmts(stmts: &mut Vec<CStmt>, dead_locals: &HashSet<String>) {
    for stmt in stmts.iter_mut() {
        prune_unused_pure_local_stmt(stmt, dead_locals);
    }
    stmts.retain(|stmt| !matches!(stmt, CStmt::Empty));
}

fn prune_unused_pure_local_stmt(stmt: &mut CStmt, dead_locals: &HashSet<String>) {
    match stmt {
        CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) => {
            if let CExpr::Var(name) = left.as_ref()
                && dead_locals.contains(&name.to_ascii_lowercase())
                && expr_is_pure_for_dead_local_prune(right)
            {
                *stmt = CStmt::Empty;
            }
        }
        CStmt::Decl { name, init, .. } => {
            if dead_locals.contains(&name.to_ascii_lowercase()) {
                match init.take() {
                    Some(expr) if !expr_is_pure_for_dead_local_prune(&expr) => {
                        *stmt = CStmt::Expr(expr);
                    }
                    _ => {
                        *stmt = CStmt::Empty;
                    }
                }
            }
        }
        CStmt::Block(stmts) => prune_unused_pure_local_stmts(stmts, dead_locals),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            prune_unused_pure_local_stmt(then_body, dead_locals);
            if let Some(else_body) = else_body {
                prune_unused_pure_local_stmt(else_body, dead_locals);
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            prune_unused_pure_local_stmt(body, dead_locals);
        }
        CStmt::For { init, body, .. } => {
            if let Some(init) = init {
                prune_unused_pure_local_stmt(init, dead_locals);
            }
            prune_unused_pure_local_stmt(body, dead_locals);
        }
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                prune_unused_pure_local_stmts(&mut case.body, dead_locals);
            }
            if let Some(default) = default {
                prune_unused_pure_local_stmts(default, dead_locals);
            }
        }
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Return(_)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
}

fn expr_is_pure_for_dead_local_prune(expr: &CExpr) -> bool {
    match expr {
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::SizeofType(_)
        | CExpr::Var(_) => true,
        CExpr::Paren(inner)
        | CExpr::AddrOf(inner)
        | CExpr::Deref(inner)
        | CExpr::Cast { expr: inner, .. }
        | CExpr::Unary { operand: inner, .. }
        | CExpr::Sizeof(inner) => expr_is_pure_for_dead_local_prune(inner),
        CExpr::Binary { left, right, .. } => {
            expr_is_pure_for_dead_local_prune(left) && expr_is_pure_for_dead_local_prune(right)
        }
        CExpr::Subscript { base, index } => {
            expr_is_pure_for_dead_local_prune(base) && expr_is_pure_for_dead_local_prune(index)
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            expr_is_pure_for_dead_local_prune(base)
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            expr_is_pure_for_dead_local_prune(cond)
                && expr_is_pure_for_dead_local_prune(then_expr)
                && expr_is_pure_for_dead_local_prune(else_expr)
        }
        CExpr::Comma(items) => items.iter().all(expr_is_pure_for_dead_local_prune),
        CExpr::Call { .. } => false,
    }
}

pub fn infer_local_struct_field_accesses(
    func: &SSAFunction,
    config: &DecompilerConfig,
) -> Vec<LocalStructFieldAccess> {
    let cfg_summary = func.cfg_risk_summary();
    if cfg_summary.block_count >= 96
        && cfg_summary.switch_block_count > 0
        && cfg_summary.max_switch_cases >= 32
    {
        return Vec::new();
    }

    let function_names = std::collections::HashMap::new();
    let strings = std::collections::HashMap::new();
    let symbols = std::collections::HashMap::new();
    let type_hints = std::collections::HashMap::new();
    let mut param_register_aliases = std::collections::HashMap::new();
    let mut arg_slot_map = std::collections::HashMap::new();

    for (idx, reg_name) in config.arg_regs.iter().enumerate() {
        let arg_name = format!("arg{}", idx + 1);
        for alias in register_alias_names(reg_name) {
            let lower = alias.to_ascii_lowercase();
            param_register_aliases.insert(lower.clone(), arg_name.clone());
            arg_slot_map.insert(lower, idx);
        }
    }

    let env = analysis::PassEnv {
        ptr_size: config.ptr_size,
        sp_name: &config.sp_name,
        fp_name: &config.fp_name,
        ret_reg_name: config.ret_regs.first().map(String::as_str).unwrap_or("rax"),
        function_names: &function_names,
        strings: &strings,
        symbols: &symbols,
        arg_regs: &config.arg_regs,
        param_register_aliases: &param_register_aliases,
        caller_saved_regs: &config.caller_saved_regs,
        type_hints: &type_hints,
        type_oracle: None,
    };

    let blocks: Vec<_> = func.blocks().cloned().collect();
    let use_info = analysis::UseInfo::analyze_for_local_struct_accesses(&blocks, &env);
    analysis::use_info::collect_local_struct_field_access_profiles(
        &use_info,
        func,
        &env,
        &arg_slot_map,
    )
    .into_iter()
    .map(|profile| LocalStructFieldAccess {
        arg_index: profile.arg_index,
        field_offset: profile.field_offset,
        access_size: profile.access_size,
        is_write: profile.is_write,
    })
    .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::SSAFunction;
    use r2types::{
        ExternalField, ExternalStruct, FunctionParamSpec, FunctionSignatureSpec, FunctionTypeFacts,
    };

    fn ssa_from_ops(ops: Vec<R2ILOp>, arch: &ArchSpec) -> SSAFunction {
        let mut block = R2ILBlock::new(0x1000, 4);
        for op in ops {
            block.push(op);
        }
        SSAFunction::from_blocks_with_arch(&[block], Some(arch))
            .expect("SSA function should build")
            .with_name("stable_demo")
    }

    fn prepared_from_ops(ops: Vec<R2ILOp>, arch: &ArchSpec) -> r2ssa::PreparedFunctionSSA {
        let mut block = R2ILBlock::new(0x1000, 4);
        for op in ops {
            block.push(op);
        }
        r2ssa::PreparedFunctionSSA::for_decompile(&[block], Some(arch))
            .expect("prepared SSA should build")
            .with_name("stable_demo")
    }

    fn test_arch_for_decompile() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::new("RDI", 0x10, 8));
        arch.add_register(RegisterDef::new("RSI", 0x18, 8));
        arch.add_register(RegisterDef::new("RBP", 0x20, 8));
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch
    }

    fn signature_spec(
        ret_type: Option<CType>,
        params: Vec<(&str, Option<CType>)>,
    ) -> FunctionSignatureSpec {
        FunctionSignatureSpec {
            ret_type: ret_type.as_ref().map(super::ctype_to_type_like),
            params: params
                .into_iter()
                .map(|(name, ty)| FunctionParamSpec {
                    name: name.to_string(),
                    ty: ty.as_ref().map(super::ctype_to_type_like),
                })
                .collect(),
        }
    }

    #[test]
    fn test_decompiler_config_default() {
        let config = DecompilerConfig::default();
        assert_eq!(config.ptr_size, 64);
        assert_eq!(config.sp_name, "rsp");
        assert_eq!(config.fp_name, "rbp");
    }

    #[test]
    fn test_decompiler_config_x86() {
        let config = DecompilerConfig::x86();
        assert_eq!(config.ptr_size, 32);
        assert_eq!(config.sp_name, "esp");
        assert_eq!(config.fp_name, "ebp");
    }

    #[test]
    fn test_decompiler_config_arm() {
        let config = DecompilerConfig::arm();
        assert_eq!(config.ptr_size, 32);
        assert_eq!(config.sp_name, "sp");
        assert_eq!(config.fp_name, "fp");
    }

    #[test]
    fn test_decompiler_config_aarch64() {
        let config = DecompilerConfig::aarch64();
        assert_eq!(config.ptr_size, 64);
        assert_eq!(config.sp_name, "sp");
        assert_eq!(config.fp_name, "x29");
        assert_eq!(config.arg_regs[0], "x0");
        assert_eq!(config.ret_regs[0], "x0");
        assert!(config.caller_saved_regs.contains("x17"));
    }

    #[test]
    fn test_decompiler_config_riscv32() {
        let config = DecompilerConfig::riscv32();
        assert_eq!(config.ptr_size, 32);
        assert_eq!(config.sp_name, "sp");
        assert_eq!(config.fp_name, "s0");
    }

    #[test]
    fn test_decompiler_config_riscv64() {
        let config = DecompilerConfig::riscv64();
        assert_eq!(config.ptr_size, 64);
        assert_eq!(config.sp_name, "sp");
        assert_eq!(config.fp_name, "s0");
    }

    #[test]
    fn reserved_param_stack_home_deref_rewrites_to_param_and_prunes_dead_pure_locals() {
        let mut func = CFunction {
            name: "dbg.test_bool_carrier_chain".to_string(),
            ret_type: CType::Int(32),
            params: vec![
                ast::CParam {
                    ty: CType::Int(32),
                    name: "x".to_string(),
                },
                ast::CParam {
                    ty: CType::Int(32),
                    name: "y".to_string(),
                },
            ],
            locals: vec![
                ast::CLocal {
                    ty: CType::Int(32),
                    name: "local_14".to_string(),
                    stack_offset: Some(-0x14),
                },
                ast::CLocal {
                    ty: CType::Int(32),
                    name: "local_18".to_string(),
                    stack_offset: Some(-0x18),
                },
                ast::CLocal {
                    ty: CType::UInt(32),
                    name: "neq".to_string(),
                    stack_offset: Some(-0x4),
                },
                ast::CLocal {
                    ty: CType::Int(64),
                    name: "widened".to_string(),
                    stack_offset: Some(-0x10),
                },
            ],
            body: vec![
                CStmt::Expr(CExpr::binary(
                    BinaryOp::Assign,
                    CExpr::Var("neq".to_string()),
                    CExpr::binary(
                        BinaryOp::Ne,
                        CExpr::Var("x".to_string()),
                        CExpr::Var("y".to_string()),
                    ),
                )),
                CStmt::Expr(CExpr::binary(
                    BinaryOp::Assign,
                    CExpr::Var("widened".to_string()),
                    CExpr::binary(
                        BinaryOp::Ne,
                        CExpr::Var("x".to_string()),
                        CExpr::Var("y".to_string()),
                    ),
                )),
                CStmt::If {
                    cond: CExpr::binary(
                        BinaryOp::Ne,
                        CExpr::Var("x".to_string()),
                        CExpr::Var("y".to_string()),
                    ),
                    then_body: Box::new(CStmt::Return(Some(CExpr::Deref(Box::new(CExpr::Var(
                        "local_14".to_string(),
                    )))))),
                    else_body: Some(Box::new(CStmt::Return(Some(CExpr::Deref(Box::new(
                        CExpr::Var("local_18".to_string()),
                    )))))),
                },
            ],
        };

        rewrite_reserved_param_stack_home_uses(
            &mut func,
            &std::collections::HashMap::from([(-0x14, "x".to_string()), (-0x18, "y".to_string())]),
            &std::collections::HashMap::new(),
            &[],
            &std::collections::BTreeMap::new(),
        );
        prune_unused_pure_locals(&mut func);

        assert!(func.locals.is_empty(), "{func:?}");
        assert_eq!(func.body.len(), 1, "{func:?}");
        let CStmt::If {
            then_body,
            else_body,
            ..
        } = &func.body[0]
        else {
            panic!("expected final if body, got {:?}", func.body);
        };
        assert_eq!(
            **then_body,
            CStmt::Return(Some(CExpr::Var("x".to_string())))
        );
        assert_eq!(
            **else_body.as_ref().expect("else branch"),
            CStmt::Return(Some(CExpr::Var("y".to_string())))
        );
    }

    #[test]
    fn authoritative_external_signature_can_shrink_recovered_header_params() {
        let recovered = vec![
            ast::CParam {
                ty: CType::Int(32),
                name: "arg1".to_string(),
            },
            ast::CParam {
                ty: CType::Int(32),
                name: "arg2".to_string(),
            },
            ast::CParam {
                ty: CType::Int(32),
                name: "arg3".to_string(),
            },
        ];
        let signature = signature_spec(
            Some(CType::Pointer(Box::new(CType::Int(8)))),
            vec![
                ("src", Some(CType::Pointer(Box::new(CType::Int(8))))),
                ("len", Some(CType::UInt(64))),
            ],
        );

        let params = merge_params_with_external_signature(recovered, Some(&signature));
        assert_eq!(
            params.len(),
            2,
            "typed/named external signature should be authoritative for the visible header"
        );
        assert_eq!(params[0].name, "src");
        assert_eq!(params[1].name, "len");
        assert!(matches!(params[1].ty, CType::UInt(64)));
    }

    #[test]
    fn generic_external_signature_does_not_shrink_richer_recovered_header_params() {
        let recovered = vec![
            ast::CParam {
                ty: CType::Int(32),
                name: "arg1".to_string(),
            },
            ast::CParam {
                ty: CType::Int(32),
                name: "arg2".to_string(),
            },
            ast::CParam {
                ty: CType::Int(32),
                name: "arg3".to_string(),
            },
        ];
        let signature = signature_spec(None, vec![("arg1", None), ("arg2", None)]);

        let params = merge_params_with_external_signature(recovered, Some(&signature));
        assert_eq!(
            params.len(),
            3,
            "generic external signature should not hide richer recovered params"
        );
        assert_eq!(params[2].name, "arg3");
    }

    #[test]
    fn external_signature_can_extend_empty_recovered_header_params() {
        let signature = signature_spec(
            None,
            vec![
                ("buf", Some(CType::Pointer(Box::new(CType::Int(8))))),
                ("count", Some(CType::UInt(64))),
            ],
        );

        let params = merge_params_with_external_signature(Vec::new(), Some(&signature));
        assert_eq!(params.len(), 2);
        assert_eq!(params[0].name, "buf");
        assert_eq!(params[1].name, "count");
    }

    #[test]
    fn decompile_is_stable_with_external_param_names_and_local_order() {
        let arch = test_arch_for_decompile();
        let func = ssa_from_ops(
            vec![
                R2ILOp::Load {
                    dst: Varnode::unique(0x10, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x20, 8),
                },
                R2ILOp::Load {
                    dst: Varnode::unique(0x11, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x28, 8),
                },
                R2ILOp::IntAdd {
                    dst: Varnode::unique(0x12, 8),
                    a: Varnode::register(0x10, 8),
                    b: Varnode::register(0x18, 8),
                },
                R2ILOp::IntAdd {
                    dst: Varnode::unique(0x13, 8),
                    a: Varnode::unique(0x12, 8),
                    b: Varnode::unique(0x10, 8),
                },
                R2ILOp::IntAdd {
                    dst: Varnode::register(0x00, 8),
                    a: Varnode::unique(0x13, 8),
                    b: Varnode::unique(0x11, 8),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x00, 8),
                },
            ],
            &arch,
        );

        let mut decompiler = Decompiler::new(DecompilerConfig::x86_64());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(CType::Int(64)),
                vec![
                    ("zzz_first", Some(CType::Int(64))),
                    ("aaa_second", Some(CType::Int(64))),
                ],
            )),
            ..FunctionTypeFacts::default()
        });

        let built_first = decompiler.build_function(&func);
        let built_second = decompiler.build_function(&func);
        let first = decompiler.decompile(&func);
        let second = decompiler.decompile(&func);

        assert_eq!(first, second, "decompiled text should be byte-stable");
        assert!(first.contains("stable_demo(int64_t zzz_first, int64_t aaa_second)"));
        assert_eq!(
            built_first
                .params
                .iter()
                .map(|param| param.name.clone())
                .collect::<Vec<_>>(),
            vec!["zzz_first".to_string(), "aaa_second".to_string()]
        );
        assert_eq!(
            built_first
                .locals
                .iter()
                .map(|local| local.name.clone())
                .collect::<Vec<_>>(),
            built_second
                .locals
                .iter()
                .map(|local| local.name.clone())
                .collect::<Vec<_>>(),
            "local declaration order should be stable across builds"
        );
    }

    #[test]
    fn decompile_is_stable_for_predicate_heavy_return() {
        let arch = test_arch_for_decompile();
        let func = ssa_from_ops(
            vec![
                R2ILOp::IntSub {
                    dst: Varnode::unique(0x20, 4),
                    a: Varnode::register(0x10, 8),
                    b: Varnode::constant(19, 4),
                },
                R2ILOp::IntEqual {
                    dst: Varnode::unique(0x21, 1),
                    a: Varnode::unique(0x20, 4),
                    b: Varnode::constant(0, 4),
                },
                R2ILOp::BoolNot {
                    dst: Varnode::unique(0x22, 1),
                    src: Varnode::unique(0x21, 1),
                },
                R2ILOp::IntZExt {
                    dst: Varnode::register(0x00, 8),
                    src: Varnode::unique(0x22, 1),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x00, 8),
                },
            ],
            &arch,
        );

        let decompiler = Decompiler::new(DecompilerConfig::x86_64());
        let first = decompiler.decompile(&func);
        let second = decompiler.decompile(&func);

        assert_eq!(first, second, "predicate-heavy text should be byte-stable");
        assert!(
            first.contains("return (int64_t)(arg1 !=") || first.contains("return arg1 != 19;"),
            "decompiled predicate should use a direct comparison, got:\n{first}"
        );
        assert!(
            !first.contains("0 != 0"),
            "decompiled predicate must not collapse into a dead boolean"
        );
        assert!(
            !first.contains("zf_"),
            "decompiled predicate should not leak flag temporaries"
        );
    }

    #[test]
    fn decompile_input_preserves_function_header_and_emits_stable_output() {
        let arch = test_arch_for_decompile();
        let ops = vec![
            R2ILOp::Load {
                dst: Varnode::unique(0x10, 8),
                space: SpaceId::Ram,
                addr: Varnode::register(0x20, 8),
            },
            R2ILOp::IntAdd {
                dst: Varnode::register(0x00, 8),
                a: Varnode::unique(0x10, 8),
                b: Varnode::register(0x18, 8),
            },
            R2ILOp::Return {
                target: Varnode::register(0x00, 8),
            },
        ];
        let func = ssa_from_ops(ops.clone(), &arch);
        let prepared = prepared_from_ops(ops, &arch);
        let type_facts = FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(CType::Int(64)),
                vec![
                    ("arg1", Some(CType::Int(64))),
                    ("arg2", Some(CType::Int(64))),
                ],
            )),
            ..FunctionTypeFacts::default()
        };
        let context = DecompilerContext::default().with_type_facts(type_facts);

        let mut legacy = Decompiler::new(DecompilerConfig::x86_64());
        legacy.set_type_facts(context.type_facts.clone());
        let input = DecompilerInput::new(prepared, context);
        let typed = Decompiler::new(DecompilerConfig::x86_64());

        let legacy_fn = legacy.build_function(&func);
        let typed_fn = typed.build_function_from_input(&input);
        let typed_text = typed.decompile_input(&input);

        assert_eq!(legacy_fn.name, typed_fn.name);
        assert_eq!(legacy_fn.ret_type, typed_fn.ret_type);
        assert_eq!(legacy_fn.params, typed_fn.params);
        assert!(typed_text.contains("stable_demo"));
        assert!(typed_text.contains("return"));
        assert!(typed_text.contains("arg2"));
    }

    #[test]
    fn explicit_external_struct_context_drives_arm64_indexed_member_rendering() {
        use std::collections::BTreeMap;

        let block = r2ssa::SSABlock {
            addr: 0x100000e40,
            size: 96,
            ops: vec![
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 2, 8),
                    a: r2ssa::SSAVar::new("X10", 1, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("X10", 2, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 2, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 2, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                SSAOp::Return {
                    target: r2ssa::SSAVar::new("X0", 0, 8),
                },
            ],
        };

        let raw = R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._test_struct_array_index");

        let struct_name = "sla_struct_explicit_demo".to_string();
        let mut type_db = ExternalTypeDb::default();
        type_db.structs.insert(
            struct_name.clone(),
            ExternalStruct {
                name: struct_name.clone(),
                fields: BTreeMap::from([
                    (
                        8,
                        ExternalField {
                            name: "third".to_string(),
                            offset: 8,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                    (
                        0x34,
                        ExternalField {
                            name: "fourteenth".to_string(),
                            offset: 0x34,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                ]),
            },
        );

        let mut decompiler = Decompiler::new(DecompilerConfig::aarch64());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(CType::Int(64)),
                vec![
                    ("arg1", Some(CType::ptr(CType::Struct(struct_name)))),
                    ("arg2", Some(CType::Int(32))),
                    ("arg3", Some(CType::Int(32))),
                ],
            )),
            external_type_db: type_db,
            ..FunctionTypeFacts::default()
        });

        let output = decompiler.decompile(&func);
        assert!(
            output.contains("struct sla_struct_explicit_demo* arg1")
                || output.contains("struct sla_struct_explicit_demo * arg1"),
            "explicit struct-typed header should survive, got:\n{output}"
        );
        assert!(
            output.contains("third"),
            "explicit external field metadata should drive member rendering, got:\n{output}"
        );
        assert!(
            !output.contains("&stack_8") && !output.contains("*(arg2 * 56"),
            "indexed member render should not fall back to stack-rooted pointer math, got:\n{output}"
        );
    }

    #[test]
    fn infer_local_struct_field_accesses_recovers_observed_arm64_struct_array_offsets() {
        let block = r2ssa::SSABlock {
            addr: 0x100000e40,
            size: 96,
            ops: vec![
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                },
                SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X8", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X11", 1, 8),
                    src: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 2, 8),
                    a: r2ssa::SSAVar::new("X10", 1, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                    src: r2ssa::SSAVar::new("X10", 2, 8),
                },
                SSAOp::IntCarry {
                    dst: r2ssa::SSAVar::new("TMPCY", 1, 1),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                },
                SSAOp::IntSCarry {
                    dst: r2ssa::SSAVar::new("TMPOV", 1, 1),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                },
                SSAOp::IntSLess {
                    dst: r2ssa::SSAVar::new("TMPNG", 1, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("TMPZR", 1, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 2, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 2, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    val: r2ssa::SSAVar::new("W8", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X8", 2, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 4, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X9", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 2, 4),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X9", 4, 8),
                    a: r2ssa::SSAVar::new("X9", 3, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:12380", 2, 8),
                    src: r2ssa::SSAVar::new("X9", 4, 8),
                },
                SSAOp::IntCarry {
                    dst: r2ssa::SSAVar::new("TMPCY", 2, 1),
                    a: r2ssa::SSAVar::new("X8", 2, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 2, 8),
                },
                SSAOp::IntSCarry {
                    dst: r2ssa::SSAVar::new("TMPOV", 2, 1),
                    a: r2ssa::SSAVar::new("X8", 2, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                    a: r2ssa::SSAVar::new("X8", 2, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 2, 8),
                },
                SSAOp::IntSLess {
                    dst: r2ssa::SSAVar::new("TMPNG", 2, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("TMPZR", 2, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X8", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 5, 8),
                    a: r2ssa::SSAVar::new("X8", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 5, 8),
                },
                SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X8", 4, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 2, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 5, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 4, 8),
                    a: r2ssa::SSAVar::new("X10", 3, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                    src: r2ssa::SSAVar::new("X10", 4, 8),
                },
                SSAOp::IntCarry {
                    dst: r2ssa::SSAVar::new("TMPCY", 3, 1),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                },
                SSAOp::IntSCarry {
                    dst: r2ssa::SSAVar::new("TMPOV", 3, 1),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                },
                SSAOp::IntSLess {
                    dst: r2ssa::SSAVar::new("TMPNG", 3, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("TMPZR", 3, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 6, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                    a: r2ssa::SSAVar::new("X9", 6, 8),
                    b: r2ssa::SSAVar::new("const:34", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                },
                SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X9", 7, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                },
                SSAOp::Return {
                    target: r2ssa::SSAVar::new("X0", 0, 8),
                },
            ],
        };

        let raw = R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._test_struct_array_index");

        let config = DecompilerConfig::aarch64();
        let function_names = std::collections::HashMap::new();
        let strings = std::collections::HashMap::new();
        let symbols = std::collections::HashMap::new();
        let type_hints = std::collections::HashMap::new();
        let mut param_register_aliases = std::collections::HashMap::new();
        let mut arg_slot_map = std::collections::HashMap::new();
        for (idx, reg_name) in config.arg_regs.iter().enumerate() {
            let arg_name = format!("arg{}", idx + 1);
            for alias in register_alias_names(reg_name) {
                let lower = alias.to_ascii_lowercase();
                param_register_aliases.insert(lower.clone(), arg_name.clone());
                arg_slot_map.insert(lower, idx);
            }
        }
        let env = analysis::PassEnv {
            ptr_size: config.ptr_size,
            sp_name: &config.sp_name,
            fp_name: &config.fp_name,
            ret_reg_name: config.ret_regs.first().map(String::as_str).unwrap_or("x0"),
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            arg_regs: &config.arg_regs,
            param_register_aliases: &param_register_aliases,
            caller_saved_regs: &config.caller_saved_regs,
            type_hints: &type_hints,
            type_oracle: None,
        };
        let blocks: Vec<_> = func.blocks().cloned().collect();
        let use_info = analysis::UseInfo::analyze(&blocks, &env);
        let profiles = analysis::use_info::collect_local_struct_field_access_profiles(
            &use_info,
            &func,
            &env,
            &arg_slot_map,
        );
        let accesses = infer_local_struct_field_accesses(&func, &config);
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x8
                && access.is_write),
            "expected store to arg0+0x8 in semantic field accesses, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x34
                && !access.is_write),
            "expected load from arg0+0x34 in semantic field accesses, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
    }

    #[test]
    fn infer_local_struct_field_accesses_recovers_observed_x86_struct_field_offsets() {
        let block = r2ssa::SSABlock {
            addr: 0x401667,
            size: 42,
            ops: vec![
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RSP", 1, 8),
                    a: r2ssa::SSAVar::new("RSP", 0, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("RSP", 1, 8),
                    val: r2ssa::SSAVar::new("RBP", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RBP", 1, 8),
                    src: r2ssa::SSAVar::new("RSP", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    val: r2ssa::SSAVar::new("RDI", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    val: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    a: r2ssa::SSAVar::new("RAX", 1, 8),
                    b: r2ssa::SSAVar::new("const:30", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    val: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 2, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 2, 8),
                    src: r2ssa::SSAVar::new("tmp:11f80", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                    a: r2ssa::SSAVar::new("RAX", 2, 8),
                    b: r2ssa::SSAVar::new("const:30", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("RAX", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("EAX", 1, 4),
                    a: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                    b: r2ssa::SSAVar::new("tmp:11f00", 2, 4),
                },
                SSAOp::Return {
                    target: r2ssa::SSAVar::new("RIP", 0, 8),
                },
            ],
        };

        let raw = R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym.test_struct_field");

        let config = DecompilerConfig::x86_64();
        let function_names = std::collections::HashMap::new();
        let strings = std::collections::HashMap::new();
        let symbols = std::collections::HashMap::new();
        let type_hints = std::collections::HashMap::new();
        let mut param_register_aliases = std::collections::HashMap::new();
        let mut arg_slot_map = std::collections::HashMap::new();
        for (idx, reg_name) in config.arg_regs.iter().enumerate() {
            let arg_name = format!("arg{}", idx + 1);
            for alias in register_alias_names(reg_name) {
                let lower = alias.to_ascii_lowercase();
                param_register_aliases.insert(lower.clone(), arg_name.clone());
                arg_slot_map.insert(lower, idx);
            }
        }
        let env = analysis::PassEnv {
            ptr_size: config.ptr_size,
            sp_name: &config.sp_name,
            fp_name: &config.fp_name,
            ret_reg_name: config.ret_regs.first().map(String::as_str).unwrap_or("rax"),
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            arg_regs: &config.arg_regs,
            param_register_aliases: &param_register_aliases,
            caller_saved_regs: &config.caller_saved_regs,
            type_hints: &type_hints,
            type_oracle: None,
        };
        let blocks: Vec<_> = func.blocks().cloned().collect();
        let use_info = analysis::UseInfo::analyze_for_local_struct_accesses(&blocks, &env);
        let profiles = analysis::use_info::collect_local_struct_field_access_profiles(
            &use_info,
            &func,
            &env,
            &arg_slot_map,
        );
        let accesses = infer_local_struct_field_accesses(&func, &config);
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0
                && !access.is_write),
            "expected load from arg0+0x0, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x30
                && access.is_write),
            "expected store to arg0+0x30, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x30
                && !access.is_write),
            "expected load from arg0+0x30, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
    }

    #[test]
    fn infer_local_struct_field_accesses_recovers_observed_x86_struct_array_offsets() {
        let block = r2ssa::SSABlock {
            addr: 0x40182f,
            size: 124,
            ops: vec![
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RSP", 1, 8),
                    a: r2ssa::SSAVar::new("RSP", 0, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("RSP", 1, 8),
                    val: r2ssa::SSAVar::new("RBP", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RBP", 1, 8),
                    src: r2ssa::SSAVar::new("RSP", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    val: r2ssa::SSAVar::new("RDI", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    val: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff0", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    val: r2ssa::SSAVar::new("EDX", 0, 4),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("EAX", 1, 4),
                    src: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("RDX", 1, 8),
                    src: r2ssa::SSAVar::new("EAX", 1, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 1, 8),
                    src: r2ssa::SSAVar::new("RDX", 1, 8),
                },
                SSAOp::IntLeft {
                    dst: r2ssa::SSAVar::new("RAX", 2, 8),
                    a: r2ssa::SSAVar::new("RAX", 1, 8),
                    b: r2ssa::SSAVar::new("const:3", 0, 8),
                },
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RAX", 3, 8),
                    a: r2ssa::SSAVar::new("RAX", 2, 8),
                    b: r2ssa::SSAVar::new("RDX", 1, 8),
                },
                SSAOp::IntLeft {
                    dst: r2ssa::SSAVar::new("RAX", 4, 8),
                    a: r2ssa::SSAVar::new("RAX", 3, 8),
                    b: r2ssa::SSAVar::new("const:3", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RDX", 2, 8),
                    src: r2ssa::SSAVar::new("RAX", 4, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 5, 8),
                    src: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("RDX", 3, 8),
                    a: r2ssa::SSAVar::new("RDX", 2, 8),
                    b: r2ssa::SSAVar::new("RAX", 5, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                    val: r2ssa::SSAVar::new("EDX", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 5, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("ECX", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 5, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 6, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:34", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("EAX", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 6, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("EAX", 3, 4),
                    a: r2ssa::SSAVar::new("EAX", 2, 4),
                    b: r2ssa::SSAVar::new("ECX", 1, 4),
                },
                SSAOp::Return {
                    target: r2ssa::SSAVar::new("RIP", 0, 8),
                },
            ],
        };

        let raw = R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym.test_struct_array_index");

        let config = DecompilerConfig::x86_64();
        let function_names = std::collections::HashMap::new();
        let strings = std::collections::HashMap::new();
        let symbols = std::collections::HashMap::new();
        let type_hints = std::collections::HashMap::new();
        let mut param_register_aliases = std::collections::HashMap::new();
        let mut arg_slot_map = std::collections::HashMap::new();
        for (idx, reg_name) in config.arg_regs.iter().enumerate() {
            let arg_name = format!("arg{}", idx + 1);
            for alias in register_alias_names(reg_name) {
                let lower = alias.to_ascii_lowercase();
                param_register_aliases.insert(lower.clone(), arg_name.clone());
                arg_slot_map.insert(lower, idx);
            }
        }
        let env = analysis::PassEnv {
            ptr_size: config.ptr_size,
            sp_name: &config.sp_name,
            fp_name: &config.fp_name,
            ret_reg_name: config.ret_regs.first().map(String::as_str).unwrap_or("rax"),
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            arg_regs: &config.arg_regs,
            param_register_aliases: &param_register_aliases,
            caller_saved_regs: &config.caller_saved_regs,
            type_hints: &type_hints,
            type_oracle: None,
        };
        let blocks: Vec<_> = func.blocks().cloned().collect();
        let use_info = analysis::UseInfo::analyze_for_local_struct_accesses(&blocks, &env);
        let profiles = analysis::use_info::collect_local_struct_field_access_profiles(
            &use_info,
            &func,
            &env,
            &arg_slot_map,
        );
        let accesses = infer_local_struct_field_accesses(&func, &config);
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x8
                && access.is_write),
            "expected store to arg0+0x8, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x8
                && !access.is_write),
            "expected load from arg0+0x8, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x34
                && !access.is_write),
            "expected load from arg0+0x34, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
    }

    #[test]
    fn infer_local_struct_field_accesses_skips_large_dense_switch_cfgs() {
        let mut blocks = Vec::new();

        let mut switch_block = R2ILBlock::new(0x1000, 1);
        switch_block.set_switch_info(r2il::SwitchInfo {
            switch_addr: 0x1000,
            min_val: 0,
            max_val: 39,
            default_target: Some(0x3000),
            cases: (0..40u64)
                .map(|idx| r2il::SwitchCase {
                    value: idx,
                    target: 0x2000 + idx * 0x10,
                })
                .collect(),
        });
        blocks.push(switch_block);

        for idx in 0..110u64 {
            let addr = if idx < 40 {
                0x2000 + idx * 0x10
            } else if idx == 40 {
                0x3000
            } else {
                0x4000 + (idx - 41) * 0x10
            };
            let mut block = R2ILBlock::new(addr, 1);
            block.push(R2ILOp::Return {
                target: Varnode::constant(0, 8),
            });
            blocks.push(block);
        }

        let func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        let accesses = infer_local_struct_field_accesses(&func, &DecompilerConfig::x86_64());
        assert!(
            accesses.is_empty(),
            "large dense switch CFGs should skip semantic local-struct inference, got {accesses:?}"
        );
    }

    #[test]
    fn decompiler_pipeline_keeps_observed_x86_struct_array_load_exprs_semantic_before_return_join()
    {
        use std::collections::HashMap;

        let block = r2ssa::SSABlock {
            addr: 0x40182f,
            size: 124,
            ops: vec![
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RSP", 1, 8),
                    a: r2ssa::SSAVar::new("RSP", 0, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("RSP", 1, 8),
                    val: r2ssa::SSAVar::new("RBP", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RBP", 1, 8),
                    src: r2ssa::SSAVar::new("RSP", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    val: r2ssa::SSAVar::new("RDI", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    val: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff0", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    val: r2ssa::SSAVar::new("EDX", 0, 4),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("EAX", 1, 4),
                    src: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("RDX", 1, 8),
                    src: r2ssa::SSAVar::new("EAX", 1, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 1, 8),
                    src: r2ssa::SSAVar::new("RDX", 1, 8),
                },
                SSAOp::IntLeft {
                    dst: r2ssa::SSAVar::new("RAX", 2, 8),
                    a: r2ssa::SSAVar::new("RAX", 1, 8),
                    b: r2ssa::SSAVar::new("const:3", 0, 8),
                },
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RAX", 3, 8),
                    a: r2ssa::SSAVar::new("RAX", 2, 8),
                    b: r2ssa::SSAVar::new("RDX", 1, 8),
                },
                SSAOp::IntLeft {
                    dst: r2ssa::SSAVar::new("RAX", 4, 8),
                    a: r2ssa::SSAVar::new("RAX", 3, 8),
                    b: r2ssa::SSAVar::new("const:3", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RDX", 2, 8),
                    src: r2ssa::SSAVar::new("RAX", 4, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 5, 8),
                    src: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("RDX", 3, 8),
                    a: r2ssa::SSAVar::new("RDX", 2, 8),
                    b: r2ssa::SSAVar::new("RAX", 5, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                    val: r2ssa::SSAVar::new("EDX", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 5, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("ECX", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 5, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 6, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:34", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("EAX", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 6, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("EAX", 3, 4),
                    a: r2ssa::SSAVar::new("EAX", 2, 4),
                    b: r2ssa::SSAVar::new("ECX", 1, 4),
                },
                SSAOp::Return {
                    target: r2ssa::SSAVar::new("RIP", 0, 8),
                },
            ],
        };

        let raw = R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops.clone();
        func = func.with_name("dbg.test_struct_array_index");

        let config = DecompilerConfig::x86_64();
        let mut decompiler = Decompiler::new(config.clone());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(CType::Int(32)),
                vec![
                    (
                        "arr",
                        Some(CType::Pointer(Box::new(CType::Struct(
                            "sla_struct_420703e08f70f00e".to_string(),
                        )))),
                    ),
                    ("idx", Some(CType::Int(32))),
                    ("v", Some(CType::Int(32))),
                ],
            )),
            external_type_db: ExternalTypeDb {
                structs: HashMap::from([(
                    "sla_struct_420703e08f70f00e".to_string(),
                    ExternalStruct {
                        name: "sla_struct_420703e08f70f00e".to_string(),
                        fields: HashMap::from([
                            (
                                8,
                                ExternalField {
                                    name: "f_8".to_string(),
                                    offset: 8,
                                    ty: Some("int32_t".to_string()),
                                },
                            ),
                            (
                                0x34,
                                ExternalField {
                                    name: "f_34".to_string(),
                                    offset: 0x34,
                                    ty: Some("int32_t".to_string()),
                                },
                            ),
                        ])
                        .into_iter()
                        .collect(),
                    },
                )]),
                ..ExternalTypeDb::default()
            },
            ..FunctionTypeFacts::default()
        });

        let normalized_func = normalize::materialize_phis(&func);
        let func = &normalized_func;

        let mut var_recovery = VariableRecovery::new_with_abi(
            &config.sp_name,
            &config.fp_name,
            config.ptr_size,
            config.arg_regs.clone(),
            config.ret_regs.clone(),
        );
        var_recovery.set_type_facts(decompiler.context.type_facts.clone());
        var_recovery.recover(func);

        let mut type_inference = TypeInference::new_with_abi(
            config.ptr_size,
            config.arg_regs.clone(),
            config.ret_regs.clone(),
        );
        type_inference
            .set_external_signature(decompiler.context.type_facts.merged_signature.clone());
        type_inference.set_external_stack_slots(decompiler.context.type_facts.stack_slots.clone());
        type_inference.set_external_type_db(decompiler.context.type_facts.external_type_db.clone());
        type_inference.set_decompile_prep_facts(func.decompile_prep_facts());
        type_inference.infer_function(func);
        let mut type_hints = type_inference
            .var_type_hints()
            .into_iter()
            .map(|(name, ty)| (name, type_like_to_ctype(&ty)))
            .collect::<HashMap<_, _>>();
        let recovered_param_infos: Vec<_> = var_recovery
            .parameters()
            .iter()
            .map(|v| {
                (
                    v.ssa_var.clone(),
                    ast::CParam {
                        ty: type_like_to_ctype(&type_inference.get_type(&v.ssa_var)),
                        name: v.name.clone(),
                    },
                )
            })
            .collect();
        let params = merge_params_with_external_signature(
            recovered_param_infos
                .iter()
                .map(|(_, param)| param.clone())
                .collect(),
            decompiler.context.type_facts.merged_signature.as_ref(),
        );
        let param_register_aliases = build_param_register_aliases(
            &params,
            &recovered_param_infos,
            &decompiler.context.type_facts.register_params,
            &config.arg_regs,
        );
        for (idx, (_ssa_var, _)) in recovered_param_infos.iter().enumerate() {
            let Some(param) = params.get(idx) else {
                continue;
            };
            let param_ty = param.ty.clone();
            type_hints.insert(param.name.clone(), param_ty.clone());
            type_hints.insert(param.name.to_ascii_lowercase(), param_ty);
        }
        for (reg_alias, param_name) in &param_register_aliases {
            let Some(param) = params.iter().find(|param| param.name == *param_name) else {
                continue;
            };
            type_hints
                .entry(reg_alias.clone())
                .or_insert_with(|| param.ty.clone());
            type_hints
                .entry(reg_alias.to_ascii_lowercase())
                .or_insert_with(|| param.ty.clone());
        }

        let known_function_signatures = HashMap::new();
        let fold_arch = FoldArchConfig {
            ptr_size: config.ptr_size,
            sp_name: config.sp_name.clone(),
            fp_name: config.fp_name.clone(),
            ret_reg_name: config
                .ret_regs
                .first()
                .cloned()
                .unwrap_or_else(|| "rax".to_string()),
            arg_regs: config.arg_regs.clone(),
            caller_saved_regs: config.caller_saved_regs.clone(),
        };
        let combined_type_oracle = type_inference.combined_type_oracle();
        let inferred_ret_type = decompiler.infer_return_type(func, &type_inference);
        let signature_ret_type = decompiler
            .context
            .type_facts
            .merged_signature
            .as_ref()
            .and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype));
        let fold_inputs = FoldInputs {
            arch: &fold_arch,
            function_names: &decompiler.context.function_names,
            strings: &decompiler.context.strings,
            symbols: &decompiler.context.symbols,
            known_function_signatures: &known_function_signatures,
            callee_facts: &decompiler.context.type_facts.callee_facts,
            stack_slots: &decompiler.context.type_facts.stack_slots,
            #[cfg(test)]
            external_stack_vars: &decompiler.context.type_facts.external_stack_vars,
            visible_bindings: &decompiler.context.type_facts.visible_bindings,
            external_type_db: &decompiler.context.type_facts.external_type_db,
            param_register_aliases: &param_register_aliases,
            type_hints: &type_hints,
            type_oracle: combined_type_oracle
                .as_ref()
                .map(|oracle| oracle as &dyn TypeOracle),
            function_return_type: signature_ret_type.as_ref().or(Some(&inferred_ret_type)),
            prepared_ssa: None,
            interproc_summary_set: None,
            prepared_semantic_view: None,
            prepared_objects: None,
            prepared_memory: None,
            prepared_predicates: None,
            prepared_call_sites: None,
        };
        let mut fold_ctx = FoldingContext::from_inputs(fold_inputs);
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        fold_ctx.analyze_blocks(&fold_blocks);
        fold_ctx.analyze_function_structure(func);

        let eax2 = fold_ctx.get_expr(&r2ssa::SSAVar::new("EAX", 2, 4));
        let ecx1 = fold_ctx.get_expr(&r2ssa::SSAVar::new("ECX", 1, 4));
        let stmts = fold_ctx.fold_block(&fold_blocks[0], fold_blocks[0].addr);
        let return_expr = stmts
            .iter()
            .find_map(|stmt| match stmt {
                CStmt::Return(Some(expr)) => Some(expr.clone()),
                _ => None,
            })
            .expect("expected return expression");
        let mut structurer = ControlFlowStructurer::new(func, &fold_ctx);
        let body_stmt = structurer.structure();
        let normalized_body_stmt = fold_ctx.normalize_final_stmt_calls(body_stmt.clone());
        let output = decompiler.decompile(func);

        assert!(
            matches!(eax2, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected decompiler pipeline get_expr(EAX_2) to keep member load, got {eax2:?}; params={params:?}; param_aliases={param_register_aliases:?}; type_hints={type_hints:?}"
        );
        assert!(
            matches!(ecx1, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected decompiler pipeline get_expr(ECX_1) to keep member load, got {ecx1:?}; params={params:?}; param_aliases={param_register_aliases:?}; type_hints={type_hints:?}"
        );
        assert!(
            format!("{return_expr:?}").contains("f_34")
                && format!("{return_expr:?}").contains("f_8"),
            "expected folded return to keep semantic member loads, got {return_expr:?}; eax2={eax2:?}; ecx1={ecx1:?}; params={params:?}; param_aliases={param_register_aliases:?}; type_hints={type_hints:?}"
        );
        assert!(
            format!("{body_stmt:?}").contains("f_34") && format!("{body_stmt:?}").contains("f_8"),
            "expected structurer body to keep semantic member loads, got {body_stmt:?}; return_expr={return_expr:?}"
        );
        assert!(
            format!("{normalized_body_stmt:?}").contains("f_34")
                && format!("{normalized_body_stmt:?}").contains("f_8"),
            "expected normalized body to keep semantic member loads, got {normalized_body_stmt:?}; body_stmt={body_stmt:?}"
        );
        assert!(
            output.contains("[idx].f_34") && output.contains("[idx].f_8"),
            "expected final decompile output to keep semantic member loads, got:\n{output}\nbody_stmt={body_stmt:?}\nnormalized_body_stmt={normalized_body_stmt:?}"
        );
    }

    #[test]
    fn decompile_observed_arm64_struct_array_keeps_indexed_member_loads() {
        let block = r2ssa::SSABlock {
            addr: 0x100000e40,
            size: 96,
            ops: vec![
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                },
                SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X8", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 2, 8),
                    a: r2ssa::SSAVar::new("X10", 1, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("X10", 2, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 2, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 2, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X8", 2, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 4, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X9", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 2, 4),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X9", 4, 8),
                    a: r2ssa::SSAVar::new("X9", 3, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                    a: r2ssa::SSAVar::new("X8", 2, 8),
                    b: r2ssa::SSAVar::new("X9", 4, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X8", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 5, 8),
                    a: r2ssa::SSAVar::new("X8", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 5, 8),
                },
                SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X8", 4, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 2, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 5, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 4, 8),
                    a: r2ssa::SSAVar::new("X10", 3, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("X10", 4, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 6, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                    a: r2ssa::SSAVar::new("X9", 6, 8),
                    b: r2ssa::SSAVar::new("const:34", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                },
                SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X9", 7, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:sum", 1, 8),
                    a: r2ssa::SSAVar::new("X8", 4, 8),
                    b: r2ssa::SSAVar::new("X9", 7, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X0", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:sum", 1, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("PC", 1, 8),
                    src: r2ssa::SSAVar::new("X30", 0, 8),
                },
                SSAOp::Return {
                    target: r2ssa::SSAVar::new("PC", 1, 8),
                },
            ],
        };

        let raw = R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._test_struct_array_index");

        let struct_name = "sla_struct_explicit_demo_full".to_string();
        let mut type_db = ExternalTypeDb::default();
        type_db.structs.insert(
            struct_name.clone(),
            ExternalStruct {
                name: struct_name.clone(),
                fields: std::collections::BTreeMap::from([
                    (
                        0,
                        ExternalField {
                            name: "f_0".to_string(),
                            offset: 0,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                    (
                        8,
                        ExternalField {
                            name: "f_8".to_string(),
                            offset: 8,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                    (
                        0x34,
                        ExternalField {
                            name: "f_34".to_string(),
                            offset: 0x34,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                ]),
            },
        );

        let mut decompiler = Decompiler::new(DecompilerConfig::aarch64());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(CType::Int(64)),
                vec![
                    ("arg1", Some(CType::ptr(CType::Struct(struct_name)))),
                    ("arg2", Some(CType::Int(32))),
                    ("arg3", Some(CType::Int(32))),
                ],
            )),
            external_type_db: type_db,
            ..FunctionTypeFacts::default()
        });

        let output = decompiler.decompile(&func);
        assert!(
            output.contains("[arg2].f_8"),
            "indexed-member path should preserve field 0x8, got:\n{output}"
        );
        assert!(
            output.contains("[arg2].f_34"),
            "indexed-member path should preserve field 0x34, got:\n{output}"
        );
        assert!(
            output.contains("return")
                && !output.contains("*(arg1 +")
                && !output.contains("arg2 * 38"),
            "observed arm64 struct-array return path should stay semantic, got:\n{output}"
        );
    }
}
