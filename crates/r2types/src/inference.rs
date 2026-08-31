//! Type inference over SSA.
//!
//! This module owns the solver-backed function/type inference engine. It
//! produces `CTypeLike` results and type/layout facts for decompiler and plugin
//! consumers; rendering-specific conversion belongs outside this crate.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{
    CTypeLike, Constraint, ConstraintSource, ExternalStackBase, ExternalStackVarSpec,
    ExternalStruct, ExternalTypeDb, FunctionSignatureSpec, FunctionType, MemoryCapability,
    ResolvedFieldLayout, ResolvedSignature, SignatureRegistry, Signedness, SolvedTypes,
    SolverConfig, StackSlotKey, Type, TypeArena, TypeId, TypeOracle, TypeSolver, to_c_type_like,
};
use r2ssa::{
    CallBoundarySlot, DecompilePrepFacts, ObjectKind, SSAFunction, SSAOp, SSAVar,
    SourceCallArgumentValue, SsaArtifact, StackAddressBase, StackAddressRoot,
};

#[derive(Debug, Clone, Default)]
struct PreparedCallTypeFlow {
    direct_target: Option<u64>,
    arguments: BTreeMap<usize, SSAVar>,
    result: Option<SSAVar>,
}

/// Type inference context.
pub struct TypeInference {
    /// Inferred types for variables.
    var_types: HashMap<SSAVar, CTypeLike>,
    /// User-provided function signatures.
    func_types: HashMap<String, FunctionType>,
    /// Function names by address (injected from external context).
    function_names: HashMap<u64, String>,
    /// Pointer size in bits.
    ptr_size: u32,
    /// Calling-convention argument registers for the active architecture.
    arg_regs: Vec<String>,
    /// Return-value registers for the active architecture.
    ret_regs: Vec<String>,
    /// Embedded signature registry.
    signature_registry: SignatureRegistry,
    /// Optional externally recovered function signature.
    external_signature: Option<FunctionSignatureSpec>,
    /// Canonical stack-slot facts keyed by structural slot identity.
    external_stack_slots: BTreeMap<StackSlotKey, ExternalStackVarSpec>,
    /// Proven SSA var -> stack-slot bindings from decompile prep.
    ssa_stack_slots: BTreeMap<SSAVar, StackSlotKey>,
    /// Exact source-owned values crossing each complete call boundary.
    ///
    /// The key is the canonical graph operation site. Register spellings and
    /// scans around a call are never used to reconstruct this flow.
    prepared_call_flows: BTreeMap<(u64, usize), PreparedCallTypeFlow>,
    /// Optional external host type database.
    external_type_db: ExternalTypeDb,
    /// What the source calls each aggregate member, by byte offset.
    source_field_names: HashMap<u64, String>,
    /// Last solver output for this function inference pass.
    solved_types: Option<SolvedTypes>,
}

pub struct CombinedTypeOracle<'a> {
    solved: &'a SolvedTypes,
    external_type_db: &'a ExternalTypeDb,
}

impl TypeInference {
    /// Create a new type inference context.
    pub fn new(ptr_size: u32) -> Self {
        let (arg_regs, ret_regs) = if ptr_size == 64 {
            (
                vec![
                    "rdi".to_string(),
                    "rsi".to_string(),
                    "rdx".to_string(),
                    "rcx".to_string(),
                    "r8".to_string(),
                    "r9".to_string(),
                ],
                vec![
                    "rax".to_string(),
                    "eax".to_string(),
                    "xmm0".to_string(),
                    "xmm0_qa".to_string(),
                    "xmm0_qb".to_string(),
                    "st0".to_string(),
                ],
            )
        } else {
            (
                vec![],
                vec!["eax".to_string(), "xmm0".to_string(), "st0".to_string()],
            )
        };
        Self::new_with_abi(ptr_size, arg_regs, ret_regs)
    }

    /// Create a new type inference context with explicit ABI register sets.
    pub fn new_with_abi(ptr_size: u32, arg_regs: Vec<String>, ret_regs: Vec<String>) -> Self {
        Self {
            var_types: HashMap::new(),
            func_types: HashMap::new(),
            function_names: HashMap::new(),
            ptr_size,
            arg_regs,
            ret_regs,
            signature_registry: SignatureRegistry::from_embedded_json(),
            external_signature: None,
            external_stack_slots: BTreeMap::new(),
            ssa_stack_slots: BTreeMap::new(),
            prepared_call_flows: BTreeMap::new(),
            external_type_db: ExternalTypeDb::default(),
            source_field_names: HashMap::new(),
            solved_types: None,
        }
    }

    /// Set externally-resolved function names (address -> symbol).
    pub fn set_function_names(&mut self, names: HashMap<u64, String>) {
        self.function_names = names;
    }

    /// Set externally recovered function signature.
    pub fn set_external_signature(&mut self, signature: Option<FunctionSignatureSpec>) {
        self.external_signature = signature;
    }

    /// Set externally recovered stack variables.
    pub fn set_external_stack_vars(&mut self, stack_vars: HashMap<i64, ExternalStackVarSpec>) {
        for (offset, spec) in stack_vars {
            self.external_stack_slots
                .entry(StackSlotKey {
                    base: spec.base.clone(),
                    offset,
                })
                .or_insert(spec);
        }
    }

    /// Set canonical externally recovered stack-slot facts.
    pub fn set_external_stack_slots(
        &mut self,
        stack_slots: BTreeMap<StackSlotKey, ExternalStackVarSpec>,
    ) {
        self.external_stack_slots = stack_slots;
    }

    /// Set SSA -> stack-slot bindings from decompile prep facts.
    pub fn set_decompile_prep_facts(&mut self, facts: Option<&DecompilePrepFacts>) {
        self.ssa_stack_slots.clear();
        let Some(facts) = facts else {
            return;
        };
        for (var, root) in &facts.stack_address_roots {
            self.ssa_stack_slots
                .insert(var.clone(), stack_slot_key_from_root(*root));
        }
    }

    /// Set SSA -> stack-slot bindings from the canonical prepared SSA artifact.
    pub fn set_prepared_ssa(&mut self, prepared: &SsaArtifact) {
        self.source_field_names = crate::prepare::source_field_names(prepared);
        self.ssa_stack_slots.clear();
        self.prepared_call_flows.clear();

        for (key, object) in &prepared.objects().value_objects {
            if key.space != r2il::SpaceId::Ram {
                continue;
            }
            let Some(object_fact) = prepared.objects().object(*object) else {
                continue;
            };
            let Some(var) = prepared.graph().value(key.value).map(|value| &value.var) else {
                continue;
            };
            let root = match object_fact.kind {
                ObjectKind::StackSlot {
                    space: r2il::SpaceId::Ram,
                    base,
                    offset,
                }
                | ObjectKind::FrameObject {
                    space: r2il::SpaceId::Ram,
                    base,
                    offset,
                } => StackAddressRoot { base, offset },
                _ => continue,
            };
            self.ssa_stack_slots
                .insert(var.clone(), stack_slot_key_from_root(root));
        }

        for boundary in prepared.facts().boundaries.calls.values() {
            if !boundary.complete {
                continue;
            }
            let Some(site) = prepared.graph().op_site_for_inst(boundary.at) else {
                continue;
            };
            let Some(call_site) = prepared.facts().call_sites.by_id.get(&boundary.call_site) else {
                continue;
            };
            if call_site.at != boundary.at {
                continue;
            }

            let mut flow = PreparedCallTypeFlow {
                direct_target: call_site.direct_target,
                ..PreparedCallTypeFlow::default()
            };
            for argument in &boundary.arguments {
                let CallBoundarySlot::Register { index, .. } = argument.slot else {
                    continue;
                };
                let SourceCallArgumentValue::Value(value) = argument.value else {
                    continue;
                };
                let Some(var) = prepared.value_var(value).cloned() else {
                    continue;
                };
                flow.arguments.insert(index as usize, var);
            }
            if let [result] = boundary.results.as_slice() {
                flow.result = prepared.value_var(result.value).cloned();
            }
            self.prepared_call_flows.insert(site, flow);
        }
    }

    /// Set externally recovered type database (from tsj payload).
    pub fn set_external_type_db(&mut self, db: ExternalTypeDb) {
        self.external_type_db = db;
    }

    /// Infer types for all variables in a function.
    pub fn infer_function(&mut self, func: &SSAFunction) {
        let mut arena = TypeArena::default();
        let mut constraints = Vec::new();

        let defs = build_def_map(func);
        let deref_consumers = collect_deref_consumers(func, &defs);
        let mut struct_hints: HashMap<SSAVar, String> = HashMap::new();

        self.emit_inferred_constraints(
            func,
            &defs,
            &deref_consumers,
            &mut arena,
            &mut constraints,
            &mut struct_hints,
        );
        self.emit_external_function_constraints(
            func,
            &mut arena,
            &mut constraints,
            &mut struct_hints,
        );
        self.emit_call_signature_constraints(func, &mut arena, &mut constraints, &mut struct_hints);

        let solver = TypeSolver::new(SolverConfig::default());
        let mut solved = solver.solve(arena, &constraints);
        let external_var_types = self.external_var_type_overrides(func);
        for (var, ty) in &external_var_types {
            let (ty_id, _) = self.type_like_to_typeid(ty, &mut solved.arena);
            solved.var_types.insert(var.clone(), ty_id);
        }

        self.var_types.clear();
        let vars = collect_vars(func);
        for var in vars {
            let ty_id = solved.type_of(&var);
            let hinted = self.type_id_to_type_like(&solved.arena, ty_id, var.size);
            self.var_types.insert(var, hinted);
        }
        for (var, ty) in external_var_types {
            self.var_types.insert(var, ty);
        }
        self.solved_types = Some(solved);
    }

    fn external_var_type_overrides(&self, func: &SSAFunction) -> HashMap<SSAVar, CTypeLike> {
        let mut overrides = HashMap::new();
        let mut reg0_map: HashMap<String, SSAVar> = HashMap::new();
        for var in collect_vars(func) {
            if var.version == 0 {
                reg0_map.entry(var.name.to_ascii_lowercase()).or_insert(var);
            }
        }

        if let Some(signature) = &self.external_signature {
            let mut occupied_param_aliases = HashSet::new();
            for (idx, ext) in signature.params.iter().enumerate() {
                let Some(ty) = &ext.ty else {
                    continue;
                };
                let Some(reg_name) = self.arg_regs.get(idx) else {
                    continue;
                };
                for alias in register_alias_names(reg_name) {
                    occupied_param_aliases.insert(alias);
                }
                if let Some(var) = reg0_map.get(&reg_name.to_ascii_lowercase()) {
                    overrides.insert(var.clone(), ty.clone());
                }
            }

            if let Some(ret_ty) = &signature.ret_type {
                for reg_name in &self.ret_regs {
                    if register_alias_names(reg_name)
                        .into_iter()
                        .any(|alias| occupied_param_aliases.contains(&alias))
                    {
                        continue;
                    }
                    if let Some(var) = reg0_map.get(&reg_name.to_ascii_lowercase()) {
                        overrides.insert(var.clone(), ret_ty.clone());
                    }
                }
            }
        }

        for var in collect_vars(func) {
            let Some(slot_spec) = self.stack_slot_spec_for_var(&var) else {
                continue;
            };
            let Some(ty) = &slot_spec.ty else {
                continue;
            };
            overrides.insert(var, ty.clone());
        }

        overrides
    }

    fn stack_slot_spec_for_var(&self, var: &SSAVar) -> Option<&ExternalStackVarSpec> {
        self.ssa_stack_slots
            .get(var)
            .and_then(|key| self.external_stack_slots.get(key))
    }

    fn emit_inferred_constraints(
        &self,
        func: &SSAFunction,
        defs: &HashMap<SSAVar, SSAOp>,
        deref_consumers: &HashMap<SSAVar, u32>,
        arena: &mut TypeArena,
        constraints: &mut Vec<Constraint>,
        struct_hints: &mut HashMap<SSAVar, String>,
    ) {
        for block in func.blocks() {
            for phi in &block.phis {
                for src in &phi.sources {
                    constraints.push(Constraint::Equal {
                        a: phi.dst.clone(),
                        b: src.1.clone(),
                        source: ConstraintSource::Inferred,
                    });
                }
            }

            for op in &block.ops {
                match op {
                    SSAOp::Copy { dst, src } | SSAOp::Cast { dst, src } => {
                        constraints.push(Constraint::Equal {
                            a: dst.clone(),
                            b: src.clone(),
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::Phi { dst, sources } => {
                        for src in sources {
                            constraints.push(Constraint::Equal {
                                a: dst.clone(),
                                b: src.clone(),
                                source: ConstraintSource::Inferred,
                            });
                        }
                    }
                    SSAOp::Load {
                        dst,
                        space: r2il::SpaceId::Ram,
                        addr,
                    } => {
                        let elem = self.integer_type_id(dst.size, Signedness::Unknown, arena);
                        constraints.push(Constraint::HasCapability {
                            ptr: addr.clone(),
                            capability: MemoryCapability::Load,
                            elem_ty: elem,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: elem,
                            source: ConstraintSource::Inferred,
                        });

                        if let Some((base, offset, stride)) = self.detect_addr_pattern(addr, defs) {
                            let field_name =
                                self.lookup_field_name(offset, dst.size, struct_hints.get(&base));
                            constraints.push(Constraint::FieldAccess {
                                base_ptr: base.clone(),
                                offset,
                                field_ty: elem,
                                field_name,
                                source: ConstraintSource::Inferred,
                            });
                            if let Some(element_size) = stride {
                                let array_elem =
                                    self.integer_type_id(element_size, Signedness::Unknown, arena);
                                let arr_ty = arena.array(array_elem, None, Some(element_size * 8));
                                let arr_ptr = arena.ptr(arr_ty);
                                constraints.push(Constraint::SetType {
                                    var: base,
                                    ty: arr_ptr,
                                    source: ConstraintSource::Inferred,
                                });
                            }
                        }
                    }
                    SSAOp::Store {
                        space: r2il::SpaceId::Ram,
                        addr,
                        val,
                    } => {
                        let elem = self.integer_type_id(val.size, Signedness::Unknown, arena);
                        constraints.push(Constraint::HasCapability {
                            ptr: addr.clone(),
                            capability: MemoryCapability::Store,
                            elem_ty: elem,
                            source: ConstraintSource::Inferred,
                        });

                        if let Some((base, offset, stride)) = self.detect_addr_pattern(addr, defs) {
                            let field_name =
                                self.lookup_field_name(offset, val.size, struct_hints.get(&base));
                            constraints.push(Constraint::FieldAccess {
                                base_ptr: base.clone(),
                                offset,
                                field_ty: elem,
                                field_name,
                                source: ConstraintSource::Inferred,
                            });
                            if let Some(element_size) = stride {
                                let array_elem =
                                    self.integer_type_id(element_size, Signedness::Unknown, arena);
                                let arr_ty = arena.array(array_elem, None, Some(element_size * 8));
                                let arr_ptr = arena.ptr(arr_ty);
                                constraints.push(Constraint::SetType {
                                    var: base,
                                    ty: arr_ptr,
                                    source: ConstraintSource::Inferred,
                                });
                            }
                        }
                    }
                    SSAOp::IntAdd { dst, a, b } | SSAOp::IntSub { dst, a, b } => {
                        if self.emit_ptr_arith_constraints_for_deref(
                            dst,
                            a,
                            b,
                            defs,
                            deref_consumers,
                            arena,
                            constraints,
                            struct_hints,
                        ) {
                            continue;
                        }

                        let ty = self.integer_type_id(dst.size, Signedness::Unknown, arena);
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: a.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: b.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::IntMult { dst, a, b }
                    | SSAOp::IntAnd { dst, a, b }
                    | SSAOp::IntOr { dst, a, b }
                    | SSAOp::IntXor { dst, a, b }
                    | SSAOp::IntLeft { dst, a, b }
                    | SSAOp::IntRight { dst, a, b }
                    | SSAOp::IntSRight { dst, a, b } => {
                        let ty = self.integer_type_id(dst.size, Signedness::Unknown, arena);
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: a.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: b.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::IntDiv { dst, a, b } | SSAOp::IntRem { dst, a, b } => {
                        let ty = self.integer_type_id(dst.size, Signedness::Unsigned, arena);
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: a.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: b.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::IntSDiv { dst, a, b } | SSAOp::IntSRem { dst, a, b } => {
                        let ty = self.integer_type_id(dst.size, Signedness::Signed, arena);
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: a.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: b.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::IntEqual { dst, a, b }
                    | SSAOp::IntNotEqual { dst, a, b }
                    | SSAOp::IntLess { dst, a, b }
                    | SSAOp::IntLessEqual { dst, a, b } => {
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: arena.bool_ty(),
                            source: ConstraintSource::Inferred,
                        });
                        let ty = self.integer_type_id(a.size, Signedness::Unknown, arena);
                        constraints.push(Constraint::SetType {
                            var: a.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: b.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::IntSLess { dst, a, b } | SSAOp::IntSLessEqual { dst, a, b } => {
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: arena.bool_ty(),
                            source: ConstraintSource::Inferred,
                        });
                        let ty = self.integer_type_id(a.size, Signedness::Signed, arena);
                        constraints.push(Constraint::SetType {
                            var: a.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: b.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::IntZExt { dst, src } => {
                        constraints.push(Constraint::SetType {
                            var: src.clone(),
                            ty: self.integer_type_id(src.size, Signedness::Unsigned, arena),
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: self.integer_type_id(dst.size, Signedness::Unsigned, arena),
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::IntSExt { dst, src } => {
                        constraints.push(Constraint::SetType {
                            var: src.clone(),
                            ty: self.integer_type_id(src.size, Signedness::Signed, arena),
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: self.integer_type_id(dst.size, Signedness::Signed, arena),
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::BoolAnd { dst, a, b }
                    | SSAOp::BoolOr { dst, a, b }
                    | SSAOp::BoolXor { dst, a, b } => {
                        let bool_ty = arena.bool_ty();
                        for var in [dst, a, b] {
                            constraints.push(Constraint::SetType {
                                var: var.clone(),
                                ty: bool_ty,
                                source: ConstraintSource::Inferred,
                            });
                        }
                    }
                    SSAOp::BoolNot { dst, src } => {
                        let bool_ty = arena.bool_ty();
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: bool_ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: src.clone(),
                            ty: bool_ty,
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::FloatAdd { dst, a, b }
                    | SSAOp::FloatSub { dst, a, b }
                    | SSAOp::FloatMult { dst, a, b }
                    | SSAOp::FloatDiv { dst, a, b } => {
                        let ty = arena.float(dst.size.saturating_mul(8));
                        for var in [dst, a, b] {
                            constraints.push(Constraint::SetType {
                                var: var.clone(),
                                ty,
                                source: ConstraintSource::Inferred,
                            });
                        }
                    }
                    SSAOp::FloatNeg { dst, src }
                    | SSAOp::FloatAbs { dst, src }
                    | SSAOp::FloatSqrt { dst, src }
                    | SSAOp::FloatCeil { dst, src }
                    | SSAOp::FloatFloor { dst, src }
                    | SSAOp::FloatRound { dst, src } => {
                        let ty = arena.float(dst.size.saturating_mul(8));
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: src.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::FloatNaN { dst, src } => {
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: arena.bool_ty(),
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: src.clone(),
                            ty: arena.float(src.size.saturating_mul(8)),
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::FloatLess { dst, a, b }
                    | SSAOp::FloatLessEqual { dst, a, b }
                    | SSAOp::FloatEqual { dst, a, b }
                    | SSAOp::FloatNotEqual { dst, a, b } => {
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: arena.bool_ty(),
                            source: ConstraintSource::Inferred,
                        });
                        let ty = arena.float(a.size.saturating_mul(8));
                        constraints.push(Constraint::SetType {
                            var: a.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: b.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::Int2Float { dst, src } => {
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: arena.float(dst.size.saturating_mul(8)),
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: src.clone(),
                            ty: self.integer_type_id(src.size, Signedness::Unknown, arena),
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::FloatFloat { dst, src } => {
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: arena.float(dst.size.saturating_mul(8)),
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: src.clone(),
                            ty: arena.float(src.size.saturating_mul(8)),
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::Float2Int { dst, src } => {
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: self.integer_type_id(dst.size, Signedness::Unknown, arena),
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: src.clone(),
                            ty: arena.float(src.size.saturating_mul(8)),
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::PtrAdd {
                        dst,
                        base,
                        index,
                        element_size,
                    }
                    | SSAOp::PtrSub {
                        dst,
                        base,
                        index,
                        element_size,
                    } => {
                        let elem = self.integer_type_id(*element_size, Signedness::Unknown, arena);
                        let ptr = arena.ptr(elem);
                        constraints.push(Constraint::SetType {
                            var: base.clone(),
                            ty: ptr,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: ptr,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: index.clone(),
                            ty: self.integer_type_id(index.size, Signedness::Unknown, arena),
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::IntNot { dst, src } | SSAOp::IntNegate { dst, src } => {
                        let ty = self.integer_type_id(dst.size, Signedness::Unknown, arena);
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: src.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::Subpiece { dst, src, .. } => {
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: self.integer_type_id(dst.size, Signedness::Unknown, arena),
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: src.clone(),
                            ty: self.integer_type_id(src.size, Signedness::Unknown, arena),
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::IntCarry { dst, a, b }
                    | SSAOp::IntSCarry { dst, a, b }
                    | SSAOp::IntSBorrow { dst, a, b } => {
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: arena.bool_ty(),
                            source: ConstraintSource::Inferred,
                        });
                        let ty = self.integer_type_id(a.size, Signedness::Unknown, arena);
                        constraints.push(Constraint::SetType {
                            var: a.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: b.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::PopCount { dst, src } | SSAOp::Lzcount { dst, src } => {
                        constraints.push(Constraint::SetType {
                            var: dst.clone(),
                            ty: self.integer_type_id(dst.size, Signedness::Unsigned, arena),
                            source: ConstraintSource::Inferred,
                        });
                        constraints.push(Constraint::SetType {
                            var: src.clone(),
                            ty: self.integer_type_id(src.size, Signedness::Unknown, arena),
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::CBranch { cond, .. } => {
                        constraints.push(Constraint::SetType {
                            var: cond.clone(),
                            ty: arena.bool_ty(),
                            source: ConstraintSource::Inferred,
                        });
                    }
                    SSAOp::Return { target } => {
                        let ty = self.integer_type_id(target.size, Signedness::Unknown, arena);
                        constraints.push(Constraint::SetType {
                            var: target.clone(),
                            ty,
                            source: ConstraintSource::Inferred,
                        });
                    }
                    _ => {}
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_ptr_arith_constraints_for_deref(
        &self,
        dst: &SSAVar,
        a: &SSAVar,
        b: &SSAVar,
        defs: &HashMap<SSAVar, SSAOp>,
        deref_consumers: &HashMap<SSAVar, u32>,
        arena: &mut TypeArena,
        constraints: &mut Vec<Constraint>,
        struct_hints: &mut HashMap<SSAVar, String>,
    ) -> bool {
        let Some(elem_size) = deref_consumers.get(dst).copied() else {
            return false;
        };
        let Some((base, offset, stride)) = self.detect_addr_pattern(dst, defs) else {
            return false;
        };

        let elem_ty = self.integer_type_id(elem_size, Signedness::Unknown, arena);
        let ptr_ty = arena.ptr(elem_ty);
        constraints.push(Constraint::SetType {
            var: dst.clone(),
            ty: ptr_ty,
            source: ConstraintSource::Inferred,
        });
        constraints.push(Constraint::SetType {
            var: base.clone(),
            ty: ptr_ty,
            source: ConstraintSource::Inferred,
        });

        if offset != 0 {
            let field_name = self.lookup_field_name(offset, elem_size, struct_hints.get(&base));
            constraints.push(Constraint::FieldAccess {
                base_ptr: base.clone(),
                offset,
                field_ty: elem_ty,
                field_name,
                source: ConstraintSource::Inferred,
            });
        }

        if let Some(element_size) = stride {
            let arr_elem = self.integer_type_id(element_size, Signedness::Unknown, arena);
            let arr_ty = arena.array(arr_elem, None, Some(element_size * 8));
            let arr_ptr = arena.ptr(arr_ty);
            constraints.push(Constraint::SetType {
                var: base.clone(),
                ty: arr_ptr,
                source: ConstraintSource::Inferred,
            });
            constraints.push(Constraint::SetType {
                var: dst.clone(),
                ty: arr_ptr,
                source: ConstraintSource::Inferred,
            });
        }

        let index_var = if a == &base {
            Some(b)
        } else if b == &base {
            Some(a)
        } else {
            None
        };
        if let Some(index_var) = index_var.filter(|v| !v.is_const()) {
            constraints.push(Constraint::SetType {
                var: index_var.clone(),
                ty: self.integer_type_id(index_var.size, Signedness::Unknown, arena),
                source: ConstraintSource::Inferred,
            });
        }

        true
    }

    fn emit_external_function_constraints(
        &self,
        func: &SSAFunction,
        arena: &mut TypeArena,
        constraints: &mut Vec<Constraint>,
        struct_hints: &mut HashMap<SSAVar, String>,
    ) {
        let Some(signature) = &self.external_signature else {
            return;
        };
        if signature.params.is_empty() && signature.ret_type.is_none() {
            return;
        }

        let vars = collect_vars(func);
        let mut reg0_map: HashMap<String, SSAVar> = HashMap::new();
        for var in vars {
            if var.version == 0 {
                reg0_map.entry(var.name.to_ascii_lowercase()).or_insert(var);
            }
        }

        for (idx, ext) in signature.params.iter().enumerate() {
            let Some(raw_ty) = &ext.ty else {
                continue;
            };
            let Some(reg_name) = self.arg_regs.get(idx) else {
                continue;
            };
            let Some(reg_var) = reg0_map.get(reg_name).cloned() else {
                continue;
            };
            let (ty_id, struct_name) = self.type_like_to_typeid(raw_ty, arena);
            constraints.push(Constraint::SetType {
                var: reg_var.clone(),
                ty: ty_id,
                source: ConstraintSource::External,
            });
            if let Some(name) = struct_name {
                struct_hints.insert(reg_var, name);
            }
        }

        for var in collect_vars(func) {
            let Some(stack_var) = self.stack_slot_spec_for_var(&var) else {
                continue;
            };
            let Some(ty) = &stack_var.ty else {
                continue;
            };
            let (ty_id, struct_name) = self.type_like_to_typeid(ty, arena);
            constraints.push(Constraint::SetType {
                var: var.clone(),
                ty: ty_id,
                source: ConstraintSource::External,
            });
            if let Some(name) = struct_name {
                struct_hints.insert(var, name);
            }
        }

        // If the external signature provides a return type, constrain return registers.
        if let Some(ret_ty) = &signature.ret_type {
            let (ty_id, _) = self.type_like_to_typeid(ret_ty, arena);
            for ret_reg in &self.ret_regs {
                if let Some(reg_var) = reg0_map.get(ret_reg).cloned() {
                    constraints.push(Constraint::SetType {
                        var: reg_var,
                        ty: ty_id,
                        source: ConstraintSource::External,
                    });
                }
            }
        }
    }

    fn emit_call_signature_constraints(
        &self,
        func: &SSAFunction,
        arena: &mut TypeArena,
        constraints: &mut Vec<Constraint>,
        struct_hints: &mut HashMap<SSAVar, String>,
    ) {
        for block in func.blocks() {
            for (call_idx, op) in block.ops.iter().enumerate() {
                let target = match op {
                    SSAOp::Call { target } | SSAOp::CallInd { target } => target,
                    _ => continue,
                };

                let Some(flow) = self.prepared_call_flows.get(&(block.addr, call_idx)) else {
                    continue;
                };
                let Some(sig) = self.resolve_call_signature(flow.direct_target, arena) else {
                    continue;
                };

                for (idx, arg_var) in &flow.arguments {
                    let Some(ty) = sig.params.get(*idx).copied() else {
                        continue;
                    };
                    constraints.push(Constraint::SetType {
                        var: arg_var.clone(),
                        ty,
                        source: ConstraintSource::SignatureRegistry,
                    });
                    if let Some(name) = struct_name_from_type(arena, ty) {
                        struct_hints.insert(arg_var.clone(), name.to_string());
                    }
                }

                let args = (0..sig.params.len())
                    .map(|index| flow.arguments.get(&index).cloned())
                    .collect::<Option<Vec<_>>>()
                    .unwrap_or_default();
                let ret = flow.result.clone().map(|ret_var| (ret_var, sig.ret));
                constraints.push(Constraint::CallSig {
                    target: target.clone(),
                    args,
                    params: sig.params,
                    ret,
                    source: ConstraintSource::SignatureRegistry,
                });
            }
        }
    }

    fn resolve_call_signature(
        &self,
        direct_target: Option<u64>,
        arena: &mut TypeArena,
    ) -> Option<ResolvedSignature> {
        let name = self.function_names.get(&direct_target?)?;

        let candidate = name.as_str();
        if let Some(sig) = self.func_types.get(candidate) {
            let params = sig
                .params
                .iter()
                .map(|ty| self.type_like_to_typeid(ty, arena).0)
                .collect();
            let ret = self.type_like_to_typeid(&sig.return_type, arena).0;
            return Some(ResolvedSignature {
                ret,
                params,
                variadic: sig.variadic,
            });
        }
        if let Some(sig) = self
            .signature_registry
            .resolve(candidate, arena, self.ptr_size)
        {
            return Some(sig);
        }

        None
    }

    /// Whether a declared field is exactly as wide as the access that reached
    /// it. An offset alone does not identify a field: an eight-byte pointer
    /// load at offset zero otherwise took the name of a four-byte member
    /// sharing that offset, and `return head` rendered as `return head->value`.
    /// A field whose type carries no scalar width is left to the offset match,
    /// which is the rule the field certificates already use.
    fn external_field_width_matches(
        &self,
        field: &crate::ExternalField,
        access_width: u32,
    ) -> bool {
        if access_width == 0 {
            return true;
        }
        field
            .ty
            .as_deref()
            .and_then(|spec| crate::facts::parse_type_like_spec(spec, self.ptr_size))
            .and_then(|ty| crate::function_facts::type_like_size_bytes(&ty, self.ptr_size))
            .is_none_or(|width| width == u64::from(access_width))
    }

    fn lookup_field_name(
        &self,
        offset: u64,
        access_width: u32,
        struct_name_hint: Option<&String>,
    ) -> Option<String> {
        // What the source called it beats anything reconstructed from offsets.
        if let Some(name) = self.source_field_names.get(&offset) {
            return Some(name.clone());
        }
        if let Some(name) = struct_name_hint {
            let key = name.to_ascii_lowercase();
            if let Some(st) = self.external_type_db.structs.get(&key)
                && let Some(field) = st.fields.get(&offset)
            {
                return self
                    .external_field_width_matches(field, access_width)
                    .then(|| field.name.clone());
            }
            if let Some(un) = self.external_type_db.unions.get(&key)
                && let Some(field) = un.fields.get(&offset)
            {
                return self
                    .external_field_width_matches(field, access_width)
                    .then(|| field.name.clone());
            }
        }

        let mut found: Option<String> = None;
        for st in self.external_type_db.structs.values() {
            if let Some(field) = st.fields.get(&offset)
                && self.external_field_width_matches(field, access_width)
            {
                if let Some(existing) = &found {
                    if existing != &field.name {
                        return None;
                    }
                } else {
                    found = Some(field.name.clone());
                }
            }
        }
        for un in self.external_type_db.unions.values() {
            if let Some(field) = un.fields.get(&offset)
                && self.external_field_width_matches(field, access_width)
            {
                if let Some(existing) = &found {
                    if existing != &field.name {
                        return None;
                    }
                } else {
                    found = Some(field.name.clone());
                }
            }
        }

        found
    }

    fn detect_addr_pattern(
        &self,
        addr: &SSAVar,
        defs: &HashMap<SSAVar, SSAOp>,
    ) -> Option<(SSAVar, u64, Option<u32>)> {
        let op = defs.get(addr)?;

        match op {
            SSAOp::PtrAdd {
                base,
                index: _,
                element_size,
                ..
            }
            | SSAOp::PtrSub {
                base,
                index: _,
                element_size,
                ..
            } => Some((base.clone(), 0, Some(*element_size))),
            SSAOp::IntAdd { a, b, .. } => {
                if a.is_const()
                    && let Some(offset) = parse_const_u64(a)
                {
                    return Some((b.clone(), offset, None));
                }
                if b.is_const()
                    && let Some(offset) = parse_const_u64(b)
                {
                    return Some((a.clone(), offset, None));
                }

                if let Some((base, stride)) = self.match_base_plus_scaled_index(a, b, defs) {
                    return Some((base, 0, Some(stride)));
                }
                if let Some((base, stride)) = self.match_base_plus_scaled_index(b, a, defs) {
                    return Some((base, 0, Some(stride)));
                }
                None
            }
            SSAOp::IntSub { a, b, .. } => {
                if b.is_const()
                    && let Some(offset) = parse_const_u64(b)
                {
                    return Some((a.clone(), offset, None));
                }
                None
            }
            _ => None,
        }
    }

    fn match_base_plus_scaled_index(
        &self,
        base: &SSAVar,
        candidate: &SSAVar,
        defs: &HashMap<SSAVar, SSAOp>,
    ) -> Option<(SSAVar, u32)> {
        let mul = defs.get(candidate)?;
        match mul {
            SSAOp::IntMult { a, b, .. } => {
                if let Some(scale) = parse_const_u64(a) {
                    return Some((base.clone(), scale as u32));
                }
                if let Some(scale) = parse_const_u64(b) {
                    return Some((base.clone(), scale as u32));
                }
                None
            }
            SSAOp::IntLeft { b, .. } => {
                let shift = parse_const_u64(b)?;
                let scale = 1u32.checked_shl(shift as u32)?;
                Some((base.clone(), scale))
            }
            _ => None,
        }
    }

    fn type_like_to_typeid(
        &self,
        ty: &CTypeLike,
        arena: &mut TypeArena,
    ) -> (TypeId, Option<String>) {
        match ty {
            CTypeLike::Void => (arena.unknown_alias("void"), None),
            CTypeLike::Bool => (arena.bool_ty(), None),
            CTypeLike::Int { bits, signedness } => (arena.int(*bits, *signedness), None),
            CTypeLike::Float(bits) => (arena.float(*bits), None),
            CTypeLike::Pointer(inner) => {
                let (inner_ty, struct_name) = self.type_like_to_typeid(inner, arena);
                (arena.ptr(inner_ty), struct_name)
            }
            CTypeLike::Array(inner, len) => {
                let (elem_ty, struct_name) = self.type_like_to_typeid(inner, arena);
                (arena.array(elem_ty, *len, None), struct_name)
            }
            CTypeLike::Struct(name) | CTypeLike::Typedef(name) => (
                arena.struct_named_or_existing(name.clone()),
                Some(name.clone()),
            ),
            CTypeLike::Union(name) | CTypeLike::Enum(name) => {
                (arena.unknown_alias(name.clone()), None)
            }
            CTypeLike::Function { .. } | CTypeLike::BitVector(_) => (arena.top(), None),
            CTypeLike::Unknown => (arena.top(), None),
        }
    }

    fn type_id_to_type_like(
        &self,
        arena: &TypeArena,
        ty_id: TypeId,
        fallback_size: u32,
    ) -> CTypeLike {
        match to_c_type_like(arena, ty_id) {
            CTypeLike::Function { .. } => CTypeLike::Unknown,
            CTypeLike::Unknown => self.type_from_size(fallback_size),
            other => other,
        }
    }

    fn integer_type_id(
        &self,
        size_bytes: u32,
        signedness: Signedness,
        arena: &mut TypeArena,
    ) -> TypeId {
        let bits = match size_bytes {
            0 => 1,
            _ => size_bytes.saturating_mul(8),
        };
        arena.int(bits, signedness)
    }

    /// Get the type of a variable.
    pub fn get_type(&self, var: &SSAVar) -> CTypeLike {
        self.var_types
            .get(var)
            .cloned()
            .unwrap_or_else(|| self.type_from_size(var.size))
    }

    /// Get a type from a size.
    pub fn type_from_size(&self, size: u32) -> CTypeLike {
        match size {
            0 => CTypeLike::Unknown,
            1 => signed_int(8),
            2 => signed_int(16),
            4 => signed_int(32),
            8 => signed_int(64),
            _ => signed_int(size.saturating_mul(8)),
        }
    }

    /// Register a function type.
    pub fn add_function_type<T: Into<FunctionType>>(&mut self, name: &str, func_type: T) {
        self.func_types.insert(name.to_string(), func_type.into());
    }

    /// Get a function type.
    pub fn get_function_type(&self, name: &str) -> Option<&FunctionType> {
        self.func_types.get(name)
    }

    /// Get the last solved type lattice for oracle-based consumers.
    pub fn solved_types(&self) -> Option<&SolvedTypes> {
        self.solved_types.as_ref()
    }

    pub fn combined_type_oracle(&self) -> Option<CombinedTypeOracle<'_>> {
        self.solved_types.as_ref().map(|solved| CombinedTypeOracle {
            solved,
            external_type_db: &self.external_type_db,
        })
    }
}

fn stack_slot_key_from_root(root: StackAddressRoot) -> StackSlotKey {
    StackSlotKey {
        base: match root.base {
            StackAddressBase::FramePointer => ExternalStackBase::FramePointer,
            StackAddressBase::StackPointer => ExternalStackBase::StackPointer,
        },
        offset: root.offset,
    }
}

impl<'a> CombinedTypeOracle<'a> {
    fn external_struct_for_type(&self, ty: TypeId) -> Option<&ExternalStruct> {
        let named = match self.solved.arena.get(ty) {
            Type::Struct(shape) => shape.name.as_deref(),
            Type::Ptr(inner) => match self.solved.arena.get(*inner) {
                Type::Struct(shape) => shape.name.as_deref(),
                _ => None,
            },
            _ => None,
        }?;
        self.external_type_db
            .structs
            .get(&named.to_ascii_lowercase())
    }
}

impl TypeOracle for CombinedTypeOracle<'_> {
    fn type_of(&self, var: &SSAVar) -> TypeId {
        self.solved.type_of(var)
    }

    fn struct_shape(&self, ty: TypeId) -> Option<&crate::StructShape> {
        self.solved.struct_shape(ty)
    }

    fn is_pointer(&self, ty: TypeId) -> bool {
        self.solved.is_pointer(ty)
    }

    fn is_array(&self, ty: TypeId) -> bool {
        self.solved.is_array(ty)
    }

    fn field_name(&self, ty: TypeId, offset: u64) -> Option<&str> {
        self.solved.field_name(ty, offset).or_else(|| {
            self.external_struct_for_type(ty)
                .and_then(|st| st.fields.get(&offset))
                .map(|field| field.name.as_str())
        })
    }

    fn field_name_any(&self, offset: u64) -> Option<&str> {
        self.solved.field_name_any(offset).or_else(|| {
            let mut matched: Option<&str> = None;
            for st in self.external_type_db.structs.values() {
                let Some(field) = st.fields.get(&offset) else {
                    continue;
                };
                match matched {
                    None => matched = Some(field.name.as_str()),
                    Some(existing) if existing == field.name => {}
                    Some(_) => return None,
                }
            }
            matched
        })
    }

    fn field_layout(&self, ty: TypeId, offset: u64) -> Option<ResolvedFieldLayout> {
        self.solved.field_layout(ty, offset).or_else(|| {
            let st = self.external_struct_for_type(ty)?;
            let field = st.fields.get(&offset)?;
            Some(ResolvedFieldLayout::direct(
                Some(st.name.clone()),
                offset,
                field.name.clone(),
            ))
        })
    }
}

fn build_def_map(func: &SSAFunction) -> HashMap<SSAVar, SSAOp> {
    let mut defs = HashMap::new();
    for block in func.blocks() {
        for op in &block.ops {
            if let Some(dst) = op.dst() {
                defs.insert(dst.clone(), op.clone());
            }
        }
        for phi in &block.phis {
            defs.insert(
                phi.dst.clone(),
                SSAOp::Phi {
                    dst: phi.dst.clone(),
                    sources: phi.sources.iter().map(|(_, src)| src.clone()).collect(),
                },
            );
        }
    }
    defs
}

fn collect_deref_consumers(
    func: &SSAFunction,
    defs: &HashMap<SSAVar, SSAOp>,
) -> HashMap<SSAVar, u32> {
    let mut out = HashMap::new();
    for block in func.blocks() {
        for op in &block.ops {
            let (addr, elem_size) = match op {
                SSAOp::Load {
                    dst,
                    space: r2il::SpaceId::Ram,
                    addr,
                } => (addr, dst.size),
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr,
                    val,
                } => (addr, val.size),
                _ => continue,
            };
            mark_deref_chain(addr, elem_size, defs, &mut out, &mut HashSet::new());
        }
    }
    out
}

fn mark_deref_chain(
    addr: &SSAVar,
    elem_size: u32,
    defs: &HashMap<SSAVar, SSAOp>,
    out: &mut HashMap<SSAVar, u32>,
    visited: &mut HashSet<SSAVar>,
) {
    let key = addr.clone();
    out.entry(key.clone())
        .and_modify(|size| *size = (*size).max(elem_size))
        .or_insert(elem_size);

    if !visited.insert(key.clone()) {
        return;
    }
    let Some(def) = defs.get(&key) else {
        return;
    };

    match def {
        SSAOp::Copy { src, .. } | SSAOp::Cast { src, .. } | SSAOp::IntZExt { src, .. } => {
            mark_deref_chain(src, elem_size, defs, out, visited);
        }
        SSAOp::IntSExt { src, .. } | SSAOp::Trunc { src, .. } => {
            mark_deref_chain(src, elem_size, defs, out, visited);
        }
        SSAOp::IntAdd { a, b, .. } => {
            if !a.is_const() {
                mark_deref_chain(a, elem_size, defs, out, visited);
            }
            if !b.is_const() {
                mark_deref_chain(b, elem_size, defs, out, visited);
            }
        }
        SSAOp::IntSub { a, .. } => {
            if !a.is_const() {
                mark_deref_chain(a, elem_size, defs, out, visited);
            }
        }
        SSAOp::PtrAdd { base, .. } | SSAOp::PtrSub { base, .. } => {
            mark_deref_chain(base, elem_size, defs, out, visited);
        }
        _ => {}
    }
}

fn collect_vars(func: &SSAFunction) -> Vec<SSAVar> {
    let mut seen = HashSet::new();
    let mut vars = Vec::new();

    let push = |v: &SSAVar, vars: &mut Vec<SSAVar>, seen: &mut HashSet<SSAVar>| {
        if seen.insert(v.clone()) {
            vars.push(v.clone());
        }
    };

    for block in func.blocks() {
        for phi in &block.phis {
            push(&phi.dst, &mut vars, &mut seen);
            for (_, src) in &phi.sources {
                push(src, &mut vars, &mut seen);
            }
        }
        for op in &block.ops {
            if let Some(dst) = op.dst() {
                push(dst, &mut vars, &mut seen);
            }
            for src in op.sources() {
                push(src, &mut vars, &mut seen);
            }
        }
    }

    vars
}

fn parse_const_offset(var: &SSAVar) -> Option<i64> {
    let val = var.constant_bits()?;
    const LIKELY_NEGATIVE_THRESHOLD: u64 = 0xffffffffffff0000;
    if val > LIKELY_NEGATIVE_THRESHOLD {
        let neg = (!val).wrapping_add(1);
        Some(-(neg as i64))
    } else {
        Some(val as i64)
    }
}

/// Every name the machine has for the storage a register names, widest form first.
pub fn register_alias_names(reg_name: &str) -> Vec<String> {
    let lower = reg_name.trim().to_ascii_lowercase();
    if lower.is_empty() {
        return Vec::new();
    }

    let aliases = match lower.as_str() {
        "rax" | "eax" | "ax" | "al" | "ah" => Some(&["rax", "eax", "ax", "al", "ah"][..]),
        "rbx" | "ebx" | "bx" | "bl" | "bh" => Some(&["rbx", "ebx", "bx", "bl", "bh"][..]),
        "rcx" | "ecx" | "cx" | "cl" | "ch" => Some(&["rcx", "ecx", "cx", "cl", "ch"][..]),
        "rdx" | "edx" | "dx" | "dl" | "dh" => Some(&["rdx", "edx", "dx", "dl", "dh"][..]),
        "rsi" | "esi" | "si" | "sil" => Some(&["rsi", "esi", "si", "sil"][..]),
        "rdi" | "edi" | "di" | "dil" => Some(&["rdi", "edi", "di", "dil"][..]),
        "rbp" | "ebp" | "bp" | "bpl" => Some(&["rbp", "ebp", "bp", "bpl"][..]),
        "rsp" | "esp" | "sp" | "spl" => Some(&["rsp", "esp", "sp", "spl"][..]),
        _ => None,
    };
    if let Some(aliases) = aliases {
        return aliases.iter().map(|alias| (*alias).to_string()).collect();
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

    // A scalar float or double in a vector register sits in the low lane, which Sleigh names apart.
    if let Some(rest) = lower.strip_prefix("xmm")
        && let Some(index) = rest.split('_').next()
        && !index.is_empty()
        && index.chars().all(|c| c.is_ascii_digit())
    {
        return vec![
            format!("xmm{index}"),
            format!("xmm{index}_da"),
            format!("xmm{index}_qa"),
        ];
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

fn signed_int(bits: u32) -> CTypeLike {
    CTypeLike::Int {
        bits,
        signedness: Signedness::Signed,
    }
}

fn parse_const_u64(var: &SSAVar) -> Option<u64> {
    parse_const_offset(var).and_then(|offset| u64::try_from(offset).ok())
}

fn struct_name_from_type(arena: &TypeArena, ty: TypeId) -> Option<&str> {
    match arena.get(ty) {
        Type::Struct(shape) => shape.name.as_deref(),
        Type::Ptr(inner) => match arena.get(*inner) {
            Type::Struct(shape) => shape.name.as_deref(),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Type;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn ssa_from_ops(ops: Vec<R2ILOp>, arch: Option<&ArchSpec>) -> SSAFunction {
        let mut block = R2ILBlock::new(0x1000, 4);
        for op in ops {
            block.push(op);
        }
        if let Some(arch) = arch {
            SSAFunction::from_blocks_with_arch(&[block], Some(arch)).expect("ssa function")
        } else {
            SSAFunction::from_blocks_raw_no_arch(&[block]).expect("ssa function")
        }
    }

    fn emit_inferred_for_test(ti: &TypeInference, func: &SSAFunction) -> Vec<Constraint> {
        let defs = build_def_map(func);
        let deref_consumers = collect_deref_consumers(func, &defs);
        let mut arena = TypeArena::default();
        let mut constraints = Vec::new();
        let mut struct_hints = HashMap::new();
        ti.emit_inferred_constraints(
            func,
            &defs,
            &deref_consumers,
            &mut arena,
            &mut constraints,
            &mut struct_hints,
        );
        constraints
    }

    fn emit_call_sig_for_test(ti: &TypeInference, func: &SSAFunction) -> Vec<Constraint> {
        let mut arena = TypeArena::default();
        let mut constraints = Vec::new();
        let mut struct_hints = HashMap::new();
        ti.emit_call_signature_constraints(func, &mut arena, &mut constraints, &mut struct_hints);
        constraints
    }

    fn test_arch_for_call_regs() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::new("RDI", 0x10, 8));
        arch.add_register(RegisterDef::new("RSI", 0x18, 8));
        arch
    }

    #[test]
    fn test_type_from_size() {
        let ti = TypeInference::new(64);

        assert_eq!(ti.type_from_size(1), signed_int(8));
        assert_eq!(ti.type_from_size(2), signed_int(16));
        assert_eq!(ti.type_from_size(4), signed_int(32));
        assert_eq!(ti.type_from_size(8), signed_int(64));
    }

    #[test]
    fn test_emit_inferred_constraints_copy_emits_equal() {
        let ti = TypeInference::new(64);
        let func = ssa_from_ops(
            vec![R2ILOp::Copy {
                dst: Varnode::unique(0x10, 4),
                src: Varnode::unique(0x11, 4),
            }],
            None,
        );
        let constraints = emit_inferred_for_test(&ti, &func);
        assert!(
            constraints
                .iter()
                .any(|c| matches!(c, Constraint::Equal { .. })),
            "copy op should emit equality constraint"
        );
    }

    #[test]
    fn test_emit_inferred_constraints_load_store_emit_has_capability() {
        let ti = TypeInference::new(64);
        let ram_addr = Varnode::unique(0x20, 8);
        let custom_addr = Varnode::unique(0x30, 8);
        let func = ssa_from_ops(
            vec![
                R2ILOp::Load {
                    dst: Varnode::unique(0x21, 4),
                    space: SpaceId::Ram,
                    addr: ram_addr.clone(),
                },
                R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: ram_addr,
                    val: Varnode::unique(0x22, 4),
                },
                R2ILOp::Load {
                    dst: Varnode::unique(0x31, 4),
                    space: SpaceId::Custom(7),
                    addr: custom_addr.clone(),
                },
                R2ILOp::Store {
                    space: SpaceId::Custom(7),
                    addr: custom_addr,
                    val: Varnode::unique(0x32, 4),
                },
            ],
            None,
        );
        let constraints = emit_inferred_for_test(&ti, &func);
        let mut ram_dst = None;
        let mut custom_dst = None;
        for op in func.blocks().flat_map(|block| &block.ops) {
            match op {
                SSAOp::Load {
                    dst,
                    space: SpaceId::Ram,
                    ..
                } => ram_dst = Some(dst),
                SSAOp::Load {
                    dst,
                    space: SpaceId::Custom(7),
                    ..
                } => custom_dst = Some(dst),
                _ => {}
            }
        }
        let ram_dst = ram_dst.expect("Ram load result");
        let custom_dst = custom_dst.expect("Custom load result");
        let cap_count = constraints
            .iter()
            .filter(|c| matches!(c, Constraint::HasCapability { .. }))
            .count();
        assert_eq!(
            cap_count, 2,
            "only the Ram load+store may emit C memory capabilities"
        );
        assert!(constraints.iter().any(
            |constraint| matches!(constraint, Constraint::SetType { var, .. } if var == ram_dst)
        ));
        assert!(!constraints.iter().any(
            |constraint| matches!(constraint, Constraint::SetType { var, .. } if var == custom_dst)
        ));
    }

    #[test]
    fn collect_deref_consumers_requires_exact_ram_space() {
        let ram_addr = Varnode::unique(0x40, 8);
        let custom_addr = Varnode::unique(0x50, 8);
        let func = ssa_from_ops(
            vec![
                R2ILOp::Load {
                    dst: Varnode::unique(0x41, 4),
                    space: SpaceId::Ram,
                    addr: ram_addr.clone(),
                },
                R2ILOp::Load {
                    dst: Varnode::unique(0x51, 8),
                    space: SpaceId::Custom(7),
                    addr: custom_addr.clone(),
                },
            ],
            None,
        );
        let defs = build_def_map(&func);
        let consumers = collect_deref_consumers(&func, &defs);
        let ram = func
            .blocks()
            .flat_map(|block| &block.ops)
            .find_map(|op| match op {
                SSAOp::Load {
                    space: SpaceId::Ram,
                    addr,
                    ..
                } => Some(addr.clone()),
                _ => None,
            })
            .expect("Ram load address");
        let custom = func
            .blocks()
            .flat_map(|block| &block.ops)
            .find_map(|op| match op {
                SSAOp::Load {
                    space: SpaceId::Custom(7),
                    addr,
                    ..
                } => Some(addr.clone()),
                _ => None,
            })
            .expect("Custom load address");

        assert_eq!(consumers.get(&ram), Some(&4));
        assert!(!consumers.contains_key(&custom));
    }

    #[test]
    fn test_emit_call_signature_constraints_tracks_args_and_return_for_call() {
        let arch = test_arch_for_call_regs();
        let mut ti = TypeInference::new(64);
        ti.set_function_names(HashMap::from([(0x401000, "test_target".to_string())]));
        ti.add_function_type(
            "test_target",
            FunctionType {
                return_type: signed_int(32),
                params: vec![signed_int(64), signed_int(64)],
                variadic: false,
            },
        );

        let func = ssa_from_ops(
            vec![
                R2ILOp::Copy {
                    dst: Varnode::register(0x10, 8),
                    src: Varnode::unique(0x30, 8),
                },
                R2ILOp::Copy {
                    dst: Varnode::register(0x18, 8),
                    src: Varnode::unique(0x31, 8),
                },
                R2ILOp::Call {
                    target: Varnode::constant(0x401000, 8),
                },
                R2ILOp::Copy {
                    dst: Varnode::unique(0x32, 8),
                    src: Varnode::register(0x00, 8),
                },
            ],
            Some(&arch),
        );

        let block = func.get_block(0x1000).expect("call block");
        let first = match &block.ops[0] {
            SSAOp::Copy { src, .. } => src.clone(),
            _ => panic!("first exact argument source"),
        };
        let second = match &block.ops[1] {
            SSAOp::Copy { src, .. } => src.clone(),
            _ => panic!("second exact argument source"),
        };
        let result = match &block.ops[3] {
            SSAOp::Copy { dst, .. } => dst.clone(),
            _ => panic!("exact result value"),
        };
        ti.prepared_call_flows.insert(
            (0x1000, 2),
            PreparedCallTypeFlow {
                direct_target: Some(0x401000),
                arguments: BTreeMap::from([(0, first), (1, second)]),
                result: Some(result),
            },
        );

        let constraints = emit_call_sig_for_test(&ti, &func);
        let call_sig = constraints
            .iter()
            .find_map(|c| match c {
                Constraint::CallSig {
                    args, params, ret, ..
                } => Some((args, params, ret)),
                _ => None,
            })
            .expect("call should emit CallSig constraint");
        assert_eq!(call_sig.0.len(), 2, "should recover two register arguments");
        assert_eq!(
            call_sig.1.len(),
            2,
            "signature should carry two parameter types"
        );
        assert!(call_sig.2.is_some(), "should recover return register flow");
    }

    #[test]
    fn call_spelling_without_source_boundary_emits_no_signature_constraints() {
        let arch = test_arch_for_call_regs();
        let mut ti = TypeInference::new(64);
        ti.set_function_names(HashMap::from([(0x401000, "test_target".to_string())]));
        ti.add_function_type(
            "test_target",
            FunctionType {
                return_type: signed_int(32),
                params: vec![signed_int(64), signed_int(64)],
                variadic: false,
            },
        );

        let func = ssa_from_ops(
            vec![
                R2ILOp::Copy {
                    dst: Varnode::register(0x10, 8),
                    src: Varnode::unique(0x40, 8),
                },
                R2ILOp::Copy {
                    dst: Varnode::register(0x18, 8),
                    src: Varnode::unique(0x41, 8),
                },
                R2ILOp::CallInd {
                    target: Varnode::constant(0x401000, 8),
                },
                R2ILOp::Copy {
                    dst: Varnode::unique(0x42, 8),
                    src: Varnode::register(0x00, 8),
                },
            ],
            Some(&arch),
        );

        assert!(
            emit_call_sig_for_test(&ti, &func).is_empty(),
            "register spellings and adjacency around a call are not a source boundary"
        );
    }

    #[test]
    fn test_parse_const_u64_uses_canonical_offset_rules() {
        assert_eq!(parse_const_u64(&SSAVar::constant(0x100, 8)), Some(0x100));
        assert_eq!(parse_const_u64(&SSAVar::constant(100, 8)), Some(100));
        assert_eq!(
            parse_const_u64(&SSAVar::constant(0xffff_ffff_ffff_ffb8, 8)),
            None
        );
        assert_eq!(
            parse_const_u64(&SSAVar::new("const:100", 0, 8)),
            None,
            "a constant-looking presentation name is not semantic evidence"
        );
    }

    #[test]
    fn test_emit_ptr_arith_constraints_for_deref_keeps_pointer_shape() {
        let ti = TypeInference::new(64);
        let mut arena = TypeArena::default();
        let mut constraints = Vec::new();
        let mut struct_hints = HashMap::new();

        let base = SSAVar::new("arg1", 0, 8);
        let offset = SSAVar::constant(0x30, 8);
        let dst = SSAVar::new("tmp:1000", 1, 8);
        let op = SSAOp::IntAdd {
            dst: dst.clone(),
            a: base.clone(),
            b: offset,
        };
        let mut defs = HashMap::new();
        defs.insert(dst.clone(), op);
        let mut deref = HashMap::new();
        deref.insert(dst.clone(), 4);

        let handled = ti.emit_ptr_arith_constraints_for_deref(
            &dst,
            &base,
            &SSAVar::constant(0x30, 8),
            &defs,
            &deref,
            &mut arena,
            &mut constraints,
            &mut struct_hints,
        );
        assert!(handled, "pointer-arithmetic deref case should be handled");

        let mut saw_field = false;
        let mut saw_dst_ptr = false;
        let mut saw_base_ptr = false;
        for c in &constraints {
            match c {
                Constraint::FieldAccess { offset, .. } => {
                    if *offset == 0x30 {
                        saw_field = true;
                    }
                }
                Constraint::SetType { var, ty, .. } if var == &dst => {
                    saw_dst_ptr = matches!(arena.get(*ty), Type::Ptr(_));
                }
                Constraint::SetType { var, ty, .. } if var == &base => {
                    saw_base_ptr = matches!(arena.get(*ty), Type::Ptr(_));
                }
                _ => {}
            }
        }

        assert!(saw_field, "should emit FieldAccess for base+const deref");
        assert!(saw_dst_ptr, "address temp should stay pointer-typed");
        assert!(saw_base_ptr, "base should stay pointer-typed");
    }

    #[test]
    fn test_detect_addr_pattern_uses_canonical_const_offsets() {
        let ti = TypeInference::new(64);
        let base = SSAVar::new("arg1", 0, 8);
        let addr = SSAVar::new("tmp:2000", 1, 8);
        let op = SSAOp::IntAdd {
            dst: addr.clone(),
            a: base.clone(),
            b: SSAVar::constant(0x100, 8),
        };
        let mut defs = HashMap::new();
        defs.insert(addr.clone(), op);

        let (detected_base, offset, stride) = ti
            .detect_addr_pattern(&addr, &defs)
            .expect("address pattern should be detected");
        assert_eq!(detected_base, base);
        assert_eq!(offset, 0x100);
        assert_eq!(stride, None);
    }

    #[test]
    fn test_emit_inferred_constraints_int_not_and_negate_emit_set_type() {
        let ti = TypeInference::new(64);
        let func = ssa_from_ops(
            vec![
                R2ILOp::IntNot {
                    dst: Varnode::unique(0x50, 4),
                    src: Varnode::unique(0x51, 4),
                },
                R2ILOp::IntNegate {
                    dst: Varnode::unique(0x52, 4),
                    src: Varnode::unique(0x53, 4),
                },
            ],
            None,
        );
        let constraints = emit_inferred_for_test(&ti, &func);
        let set_type_count = constraints
            .iter()
            .filter(|c| matches!(c, Constraint::SetType { .. }))
            .count();
        assert!(
            set_type_count >= 4,
            "IntNot + IntNegate should emit at least 4 SetType constraints (dst+src each), got {}",
            set_type_count
        );
    }

    #[test]
    fn test_emit_inferred_constraints_carry_ops_emit_bool_dst() {
        let ti = TypeInference::new(64);
        let func = ssa_from_ops(
            vec![R2ILOp::IntCarry {
                dst: Varnode::unique(0x60, 1),
                a: Varnode::unique(0x61, 4),
                b: Varnode::unique(0x62, 4),
            }],
            None,
        );
        let constraints = emit_inferred_for_test(&ti, &func);
        let has_bool = constraints.iter().any(|c| match c {
            Constraint::SetType { ty, .. } => {
                let arena = TypeArena::default();
                let bool_id = arena.bool_ty();
                *ty == bool_id
            }
            _ => false,
        });
        assert!(has_bool, "IntCarry should emit Bool type for dst");
    }

    #[test]
    fn test_emit_inferred_constraints_cbranch_emits_bool_for_cond() {
        let ti = TypeInference::new(64);
        let cond = Varnode::unique(0x70, 1);
        let target = Varnode::constant(0x2000, 8);
        let func = ssa_from_ops(
            vec![R2ILOp::CBranch {
                target,
                cond: cond.clone(),
            }],
            None,
        );
        let constraints = emit_inferred_for_test(&ti, &func);
        let has_bool = constraints.iter().any(|c| match c {
            Constraint::SetType { ty, .. } => {
                let arena = TypeArena::default();
                let bool_id = arena.bool_ty();
                *ty == bool_id
            }
            _ => false,
        });
        assert!(
            has_bool,
            "CBranch should emit Bool type constraint for cond"
        );
    }

    #[test]
    fn test_emit_inferred_constraints_return_emits_integer_type() {
        let ti = TypeInference::new(64);
        let func = ssa_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::register(0x00, 8),
            }],
            None,
        );
        let constraints = emit_inferred_for_test(&ti, &func);
        let has_set = constraints
            .iter()
            .any(|c| matches!(c, Constraint::SetType { .. }));
        assert!(has_set, "Return should emit SetType for target register");
    }

    #[test]
    fn test_emit_inferred_constraints_subpiece_emits_types() {
        let ti = TypeInference::new(64);
        let func = ssa_from_ops(
            vec![R2ILOp::Subpiece {
                dst: Varnode::unique(0x80, 4),
                src: Varnode::unique(0x81, 8),
                offset: 0,
            }],
            None,
        );
        let constraints = emit_inferred_for_test(&ti, &func);
        let set_type_count = constraints
            .iter()
            .filter(|c| matches!(c, Constraint::SetType { .. }))
            .count();
        assert!(
            set_type_count >= 2,
            "Subpiece should emit at least 2 SetType constraints (dst+src), got {}",
            set_type_count
        );
    }

    #[test]
    fn test_legacy_external_stack_vars_are_canonicalized_without_name_fallback() {
        let mut ti = TypeInference::new(64);
        let slot_var = SSAVar::new("tmp:stack", 1, 8);
        ti.set_external_stack_vars(HashMap::from([(
            -8,
            ExternalStackVarSpec {
                name: "count".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 32,
                    signedness: Signedness::Signed,
                }),
                base: ExternalStackBase::FramePointer,
                role: crate::ExternalStackSlotRole::Local,
                param_index: None,
                param_name: None,
                source_reg: None,
            },
        )]));
        ti.ssa_stack_slots.insert(
            slot_var.clone(),
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -8,
            },
        );

        assert_eq!(
            ti.stack_slot_spec_for_var(&slot_var)
                .map(|slot| slot.name.as_str()),
            Some("count")
        );
        assert!(
            ti.stack_slot_spec_for_var(&SSAVar::new("count", 1, 8))
                .is_none(),
            "legacy offset-only metadata must not bind unrelated SSA vars by name"
        );
    }

    #[test]
    fn set_prepared_ssa_uses_canonical_stack_objects_for_slot_binding() {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RBP", 0x20, 8));
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch.add_register(RegisterDef::new("RIP", 0x30, 8));

        let register_storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let frame_pointer = register_storage(0x20);
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"canonical-stack-object-fixture".to_vec(),
            "sysv64",
            [],
            r2ssa::SourceFunctionReturn::Void,
            [r2ssa::SourceStackSlotSpec::new_local(
                r2ssa::StackAddressBase::FramePointer,
                frame_pointer,
                -16,
                4,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(register_storage(0x30)))
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(0x28)))
        .and_then(|interface| interface.with_frame_pointer_storage(frame_pointer))
        .expect("exact local-stack interface");

        let prepared = SsaArtifact::for_decompile_with_interface(
            &[R2ILBlock {
                addr: 0x2000,
                size: 4,
                ops: vec![
                    R2ILOp::IntSub {
                        dst: Varnode::unique(0x10, 8),
                        a: Varnode::register(0x20, 8),
                        b: Varnode::constant(0x10, 8),
                    },
                    R2ILOp::Load {
                        dst: Varnode::unique(0x18, 4),
                        space: r2il::SpaceId::Ram,
                        addr: Varnode::unique(0x10, 8),
                    },
                    R2ILOp::Return {
                        target: Varnode::constant(0, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            Some(&arch),
            interface,
        )
        .expect("prepared SSA");

        let mut ti = TypeInference::new(64);
        ti.set_external_stack_slots(BTreeMap::from([(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -16,
            },
            ExternalStackVarSpec {
                name: "slot".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 32,
                    signedness: Signedness::Signed,
                }),
                base: ExternalStackBase::FramePointer,
                role: crate::ExternalStackSlotRole::Local,
                param_index: None,
                param_name: None,
                source_reg: None,
            },
        )]));
        ti.set_prepared_ssa(&prepared);

        let slot_var = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.name_kind().is_temporary())
            .map(|value| value.var.clone())
            .expect("stack-root value");
        assert_eq!(
            ti.stack_slot_spec_for_var(&slot_var)
                .map(|slot| slot.name.as_str()),
            Some("slot")
        );
    }

    #[test]
    fn set_prepared_ssa_does_not_turn_custom_space_roots_into_stack_slots() {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RBP", 0x20, 8));
        let prepared = SsaArtifact::for_decompile(
            &[R2ILBlock {
                addr: 0x2100,
                size: 4,
                ops: vec![
                    R2ILOp::IntSub {
                        dst: Varnode::unique(0x10, 8),
                        a: Varnode::register(0x20, 8),
                        b: Varnode::constant(0x10, 8),
                    },
                    R2ILOp::Load {
                        dst: Varnode::unique(0x18, 4),
                        space: r2il::SpaceId::Custom(7),
                        addr: Varnode::unique(0x10, 8),
                    },
                    R2ILOp::Return {
                        target: Varnode::constant(0, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            Some(&arch),
        )
        .expect("prepared custom-space SSA");
        let mut ti = TypeInference::new(64);
        ti.set_external_stack_slots(BTreeMap::from([(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -16,
            },
            ExternalStackVarSpec {
                name: "slot".to_string(),
                ty: None,
                base: ExternalStackBase::FramePointer,
                role: crate::ExternalStackSlotRole::Local,
                param_index: None,
                param_name: None,
                source_reg: None,
            },
        )]));
        ti.set_prepared_ssa(&prepared);
        let address = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.name_kind().is_temporary() && value.var.size == 8)
            .map(|value| value.var.clone())
            .expect("custom address root");
        assert!(ti.stack_slot_spec_for_var(&address).is_none());
    }
}
