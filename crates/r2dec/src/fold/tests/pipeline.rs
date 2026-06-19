#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

    use crate::{
        FoldArchConfig, FoldInputs,
        analysis::{
            CallOwner, CallOwnerKind, CallOwnershipFact, CallSiteId, PassEnv,
            PreparedSemanticView, ScalarValue, StackInfo, StackSlotProvenance, StackSlotValueKind,
            UseInfo,
        },
    };
    use crate::fold::context::EffectRenderProofKind;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2types::{
        CalleeArgEffect, CalleeFact, CalleeReturnRelation, ExternalField, ExternalStackBase,
        ExternalStackVarSpec, ExternalStruct, ExternalTypeDb, FunctionParamSpec,
        FunctionSignatureSpec, FunctionTypeFacts, Signedness, SolvedTypes, SolverDiagnostics,
        StackSlotKey, StructShape, TypeArena, TypeId, TypeOracle, VisibleBinding,
        VisibleBindingKind,
    };
    use crate::fold::PtrArith;

    #[derive(Debug, Clone)]
    struct FunctionType {
        return_type: CType,
        params: Vec<CType>,
        variadic: bool,
    }

    impl From<FunctionType> for r2types::FunctionType {
        fn from(value: FunctionType) -> Self {
            Self {
                return_type: crate::ctype_to_type_like(&value.return_type),
                params: value.params.iter().map(crate::ctype_to_type_like).collect(),
                variadic: value.variadic,
            }
        }
    }

    fn make_var(name: &str, version: u32, size: u32) -> SSAVar {
        SSAVar::new(name, version, size)
    }

    fn make_block(ops: Vec<SSAOp>) -> SSABlock {
        SSABlock {
            addr: 0x1000,
            size: 4,
            ops,
            phis: Vec::new(),
        }
    }

    fn make_test_arch_x86_64() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::sub("EAX", 0x00, 4, "RAX"));
        arch.add_register(RegisterDef::new("RDI", 0x10, 8));
        arch.add_register(RegisterDef::sub("EDI", 0x10, 4, "RDI"));
        arch.add_register(RegisterDef::new("RSI", 0x18, 8));
        arch.add_register(RegisterDef::sub("ESI", 0x18, 4, "RSI"));
        arch.add_register(RegisterDef::new("RBP", 0x20, 8));
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch
    }

    fn make_test_arch_aarch64_kernel_regs() -> ArchSpec {
        let mut arch = ArchSpec::new("aarch64");
        arch.add_register(RegisterDef::new("x0", 0x4000, 8));
        arch.add_register(RegisterDef::sub("w0", 0x4000, 4, "x0"));
        arch.add_register(RegisterDef::new("x8", 0x4040, 8));
        arch.add_register(RegisterDef::sub("w8", 0x4040, 4, "x8"));
        arch.add_register(RegisterDef::new("x20", 0x40a0, 8));
        arch.add_register(RegisterDef::sub("w20", 0x40a0, 4, "x20"));
        arch.add_register(RegisterDef::new("x30", 0x40f0, 8));
        arch
    }

    fn prepared_from_r2il_blocks(
        blocks: &[R2ILBlock],
        arch: &ArchSpec,
    ) -> r2ssa::SsaArtifact {
        r2ssa::SsaArtifact::for_decompile(blocks, Some(arch))
            .expect("prepared SSA should build")
    }

    fn call_arg(expr: CExpr) -> crate::analysis::CallArgBinding {
        crate::analysis::CallArgBinding::from(expr)
    }

    fn stack_load_call_arg(offset: i64, size: u32) -> crate::analysis::CallArgBinding {
        crate::analysis::CallArgBinding::input(crate::analysis::SemanticCallArg::semantic(
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::StackSlot(offset),
                    index: None,
                    scale_bytes: 0,
                    offset_bytes: 0,
                },
                size,
            },
        ))
    }

    fn result_call_arg(
        expr: CExpr,
        source_call: (u64, usize),
        stack_offset: i64,
    ) -> crate::analysis::CallArgBinding {
        crate::analysis::CallArgBinding::result(crate::analysis::SemanticCallArg::FallbackExpr(
            expr,
        ))
        .with_source_call(source_call.0, source_call.1)
        .with_stack_offset(stack_offset)
    }

    fn stack_var_spec(name: &str, ty: Option<CType>, base: Option<&str>) -> ExternalStackVarSpec {
        ExternalStackVarSpec {
            name: name.to_string(),
            ty: ty.as_ref().map(crate::ctype_to_type_like),
            base: match base.map(|raw| raw.to_ascii_lowercase()) {
                Some(raw) if raw == "rbp" || raw == "ebp" || raw == "bp" || raw == "fp" => {
                    r2types::ExternalStackBase::FramePointer
                }
                Some(raw) if raw == "rsp" || raw == "esp" || raw == "sp" => {
                    r2types::ExternalStackBase::StackPointer
                }
                Some(raw) => r2types::ExternalStackBase::Named(raw),
                None => r2types::ExternalStackBase::default(),
            },
            role: r2types::ExternalStackSlotRole::Unknown,
            param_index: None,
            param_name: None,
            source_reg: None,
        }
    }

    fn signature_spec(
        ret: Option<CType>,
        params: Vec<(&str, Option<CType>)>,
    ) -> FunctionSignatureSpec {
        FunctionSignatureSpec {
            ret_type: ret.as_ref().map(crate::ctype_to_type_like),
            params: params
                .into_iter()
                .map(|(name, ty)| FunctionParamSpec {
                    name: name.to_string(),
                    ty: ty.as_ref().map(crate::ctype_to_type_like),
                })
            .collect(),
        }
    }

    fn minimal_callee_fact(addr: u64, name: &str) -> CalleeFact {
        CalleeFact {
            function_id: addr,
            name: Some(name.to_string()),
            direct_callees: Vec::new(),
            callsite_count: 1,
            has_unknown_calls: false,
            arg_effects: BTreeMap::new(),
            memory_effects: Vec::new(),
            transfer_effects: Vec::new(),
            allocation_effects: Vec::new(),
            lifetime_effects: Vec::new(),
            sync_effects: Vec::new(),
            atomic_effects: Vec::new(),
            param_type_hints: BTreeMap::new(),
            return_type_hint: None,
            return_relation: CalleeReturnRelation::Unknown,
            reads_global_memory: false,
            writes_global_memory: false,
            touches_unknown_memory: false,
        }
    }

    fn external_signature_certificate(
        signature: &FunctionSignatureSpec,
    ) -> Option<r2types::SignatureCertificate> {
        r2types::SignatureCertificate::from_signature(
            signature,
            [r2types::SignatureCertificateSource::ExternalContext],
        )
    }

    fn visible_stack_binding(name: &str, ty: Option<CType>, offset: i64) -> VisibleBinding {
        VisibleBinding {
            name: name.to_string(),
            ty: ty.as_ref().map(crate::ctype_to_type_like),
            kind: VisibleBindingKind::Local,
            stack_slot: Some(StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset,
            }),
            param_index: None,
            source_reg: None,
        }
    }

    fn make_oracle_for_member(base: SSAVar, offset: u64, field_name: &str) -> SolvedTypes {
        let mut arena = TypeArena::default();
        let i32_ty = arena.int(32, Signedness::Signed);
        let st = arena.struct_named_or_existing("DemoStruct");
        let st = arena.struct_with_field(st, offset, Some(field_name.to_string()), i32_ty);
        let ptr = arena.ptr(st);
        let mut var_types = HashMap::new();
        var_types.insert(base, ptr);
        let top_id = arena.top();
        SolvedTypes {
            arena,
            var_types,
            diagnostics: SolverDiagnostics::default(),
            top_id,
        }
    }

    #[allow(dead_code)]
    fn make_oracle_for_members(base: SSAVar, fields: &[(u64, &str)]) -> SolvedTypes {
        let mut arena = TypeArena::default();
        let i32_ty = arena.int(32, Signedness::Signed);
        let mut st = arena.struct_named_or_existing("DemoStruct");
        for (offset, field_name) in fields {
            st = arena.struct_with_field(st, *offset, Some((*field_name).to_string()), i32_ty);
        }
        let ptr = arena.ptr(st);
        let mut var_types = HashMap::new();
        var_types.insert(base, ptr);
        let top_id = arena.top();
        SolvedTypes {
            arena,
            var_types,
            diagnostics: SolverDiagnostics::default(),
            top_id,
        }
    }

    fn make_aarch64_ctx<'a>() -> FoldingContext<'a> {
        let arch = Box::leak(Box::new(FoldArchConfig {
            ptr_size: 8,
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            ret_reg_name: "x0".to_string(),
            arg_regs: vec![
                "x0".to_string(),
                "x1".to_string(),
                "x2".to_string(),
                "x3".to_string(),
                "x4".to_string(),
                "x5".to_string(),
                "x6".to_string(),
                "x7".to_string(),
            ],
            caller_saved_regs: HashSet::new(),
        }));
        let empty_u64 = Box::leak(Box::new(HashMap::new()));
        let empty_stack = Box::leak(Box::new(HashMap::new()));
        let empty_stack_slots = Box::leak(Box::new(BTreeMap::new()));
        let empty_visible = Box::leak(Box::new(Vec::new()));
        let empty_str = Box::leak(Box::new(HashMap::new()));
        let empty_fn = Box::leak(Box::new(HashMap::new()));
        let empty_callee = Box::leak(Box::new(BTreeMap::new()));
        let empty_ty = Box::leak(Box::new(HashMap::new()));
        FoldingContext::from_inputs(FoldInputs {
            arch,
            function_names: empty_u64,
            strings: empty_u64,
            symbols: empty_u64,
            known_function_signatures: empty_fn,
            callee_facts: empty_callee,
            callee_resolution: None,
            stack_slots: empty_stack_slots,
            external_stack_vars: empty_stack,
            visible_bindings: empty_visible,
            external_type_db: Box::leak(Box::new(r2types::ExternalTypeDb::default())),
            semantic_artifact: None,
            param_register_aliases: empty_str,
            type_hints: empty_ty,
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
        })
    }

    fn make_x86_64_ctx<'a>() -> FoldingContext<'a> {
        let arch = Box::leak(Box::new(FoldArchConfig {
            ptr_size: 8,
            sp_name: "rsp".to_string(),
            fp_name: "rbp".to_string(),
            ret_reg_name: "rax".to_string(),
            arg_regs: vec![
                "rdi".to_string(),
                "rsi".to_string(),
                "rdx".to_string(),
                "rcx".to_string(),
                "r8".to_string(),
                "r9".to_string(),
            ],
            caller_saved_regs: HashSet::new(),
        }));
        let empty_u64 = Box::leak(Box::new(HashMap::new()));
        let empty_stack = Box::leak(Box::new(HashMap::new()));
        let empty_stack_slots = Box::leak(Box::new(BTreeMap::new()));
        let empty_visible = Box::leak(Box::new(Vec::new()));
        let empty_str = Box::leak(Box::new(HashMap::new()));
        let empty_fn = Box::leak(Box::new(HashMap::new()));
        let empty_callee = Box::leak(Box::new(BTreeMap::new()));
        let empty_ty = Box::leak(Box::new(HashMap::new()));
        FoldingContext::from_inputs(FoldInputs {
            arch,
            function_names: empty_u64,
            strings: empty_u64,
            symbols: empty_u64,
            known_function_signatures: empty_fn,
            callee_facts: empty_callee,
            callee_resolution: None,
            stack_slots: empty_stack_slots,
            external_stack_vars: empty_stack,
            visible_bindings: empty_visible,
            external_type_db: Box::leak(Box::new(r2types::ExternalTypeDb::default())),
            semantic_artifact: None,
            param_register_aliases: empty_str,
            type_hints: empty_ty,
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
        })
    }

    fn make_x86_64_ctx_with_prepared<'a>(
        prepared_ssa: &'a r2ssa::SsaArtifact,
    ) -> FoldingContext<'a> {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_ssa = Some(prepared_ssa);
        ctx
    }

    fn make_aarch64_ctx_with_prepared<'a>(
        prepared_ssa: &'a r2ssa::SsaArtifact,
    ) -> FoldingContext<'a> {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.prepared_ssa = Some(prepared_ssa);
        ctx
    }

    fn configure_aarch64_helper_printf_ctx(
        ctx: &mut FoldingContext<'_>,
        helper_addr: u64,
        helper_name: &str,
        helper_param_count: usize,
        format_addr: u64,
        format: &str,
        stack_vars: &[(i64, &str)],
    ) {
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (helper_addr, helper_name.to_string()),
            (0x10000259c, "sym.imp.printf".to_string()),
            (0x1000025d8, "sym.imp.atoi".to_string()),
        ])));
        ctx.inputs.strings =
            Box::leak(Box::new(HashMap::from([(format_addr, format.to_string())])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                helper_name.to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::Int(32); helper_param_count],
                    variadic: false,
                },
            ),
            (
                "sym.imp.printf".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: true,
                },
            ),
            (
                "sym.imp.atoi".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: false,
                },
            ),
        ]));
        ctx.set_external_stack_vars(
            stack_vars
                .iter()
                .map(|(offset, name)| {
                    (
                        *offset,
                        stack_var_spec(name, Some(CType::Int(32)), Some("x29")),
                    )
                })
                .collect(),
        );
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([
            ("x0".to_string(), "argc".to_string()),
            ("x1".to_string(), "argv".to_string()),
            ("x2".to_string(), "envp".to_string()),
        ])));
        ctx.inputs.type_hints = Box::leak(Box::new(HashMap::from([
            ("argc".to_string(), CType::Int(32)),
            ("argv".to_string(), CType::ptr(CType::ptr(CType::Int(8)))),
            ("envp".to_string(), CType::ptr(CType::ptr(CType::Int(8)))),
        ])));
    }

    #[test]
    fn visible_stack_slot_sharing_requires_known_matching_offsets() {
        let mut ctx = make_x86_64_ctx();
        ctx.state.analysis_ctx.stack_info.stack_vars = HashMap::from([
            (-8, "buf".to_string()),
            (-16, "len".to_string()),
        ]);

        assert!(ctx.visible_names_share_stack_slot("buf", "local_8"));
        assert!(!ctx.visible_names_share_stack_slot("buf", "len"));
        assert!(!ctx.visible_names_share_stack_slot("not_stack_a", "not_stack_b"));
    }

    #[test]
    fn scalar_stack_read_modify_write_drops_addr_of_aliases() {
        let mut ctx = make_x86_64_ctx();
        ctx.set_external_stack_vars(HashMap::from([
            (-8, stack_var_spec("sum", Some(CType::Int(32)), Some("rbp"))),
            (-4, stack_var_spec("i", Some(CType::Int(32)), Some("rbp"))),
        ]));
        ctx.inputs.visible_bindings = Box::leak(Box::new(vec![
            visible_stack_binding("sum", Some(CType::Int(32)), -8),
            visible_stack_binding("i", Some(CType::Int(32)), -4),
        ]));
        ctx.set_type_hints(HashMap::from([
            ("sum".to_string(), CType::Int(32)),
            ("i".to_string(), CType::Int(32)),
        ]));
        ctx.state.analysis_ctx.stack_info.stack_vars = HashMap::from([
            (-8, "sum".to_string()),
            (-4, "i".to_string()),
        ]);

        let sum_rhs = ctx.collapse_scalar_stack_addr_artifact(CExpr::binary(
            BinaryOp::Add,
            CExpr::AddrOf(Box::new(CExpr::Var("sum".to_string()))),
            CExpr::Subscript {
                base: Box::new(CExpr::Var("arr".to_string())),
                index: Box::new(CExpr::Var("i".to_string())),
            },
        ));
        let i_rhs = ctx.rewrite_scalar_stack_placeholder_rhs(
            &CExpr::Var("i".to_string()),
            CExpr::Var("local_3".to_string()),
        );
        let cross_slot_rhs = ctx.rewrite_scalar_stack_placeholder_rhs(
            &CExpr::Var("sum".to_string()),
            CExpr::Var("local_17".to_string()),
        );

        assert!(
            expr_contains_var(&sum_rhs, "sum") && !expr_contains_addr_of(&sum_rhs),
            "scalar sum update should not expose address aliases: {sum_rhs:?}"
        );
        assert!(
            expr_contains_var(&i_rhs, "i") && !expr_contains_addr_of(&i_rhs),
            "scalar loop increment should not expose address aliases: {i_rhs:?}"
        );
        assert!(
            matches!(
                &i_rhs,
                CExpr::Binary {
                    op: BinaryOp::Add,
                    left,
                    right,
                } if matches!(left.as_ref(), CExpr::Var(name) if name == "i")
                    && matches!(right.as_ref(), CExpr::IntLit(1))
            ),
            "scalar loop increment should render as `i + 1`: {i_rhs:?}"
        );
        assert_eq!(
            cross_slot_rhs,
            CExpr::Var("local_17".to_string()),
            "large cross-slot placeholder deltas must not be rewritten as scalar arithmetic"
        );
    }

    #[test]
    fn canonical_frame_stack_slot_offsets_are_rmw_candidates() {
        let mut ctx = make_x86_64_ctx();
        ctx.set_external_stack_vars(HashMap::from([(
            -8,
            stack_var_spec("count", Some(CType::UInt(64)), Some("rbp")),
        )]));
        ctx.state.analysis_ctx.stack_info.stack_vars =
            HashMap::from([(-8, "count".to_string())]);

        let offsets = ctx.stack_offsets_for_visible_storage_name("count");
        assert!(offsets.contains(&-8), "keeps derived offset: {offsets:?}");
        assert!(
            offsets.contains(&8),
            "canonical frame-pointer stack slot should be available as an RMW proof candidate: {offsets:?}"
        );
    }

    fn expr_contains_binary_op(expr: &CExpr, target: BinaryOp) -> bool {
        match expr {
            CExpr::Binary { op, left, right } => {
                *op == target
                    || expr_contains_binary_op(left, target)
                    || expr_contains_binary_op(right, target)
            }
            CExpr::Unary { operand, .. } => expr_contains_binary_op(operand, target),
            CExpr::Paren(inner) => expr_contains_binary_op(inner, target),
            CExpr::Cast { expr: inner, .. } => expr_contains_binary_op(inner, target),
            _ => false,
        }
    }

    fn expr_contains_flag_artifact(expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                let lower = name.to_lowercase();
                lower.starts_with("of_")
                    || lower.starts_with("zf_")
                    || lower.starts_with("sf_")
                    || lower.starts_with("cf_")
            }
            CExpr::Binary { left, right, .. } => {
                expr_contains_flag_artifact(left) || expr_contains_flag_artifact(right)
            }
            CExpr::Unary { operand, .. } => expr_contains_flag_artifact(operand),
            CExpr::Paren(inner) => expr_contains_flag_artifact(inner),
            CExpr::Cast { expr: inner, .. } => expr_contains_flag_artifact(inner),
            CExpr::Deref(inner) => expr_contains_flag_artifact(inner),
            CExpr::Subscript { base, index } => {
                expr_contains_flag_artifact(base) || expr_contains_flag_artifact(index)
            }
            CExpr::Member { base, .. } => expr_contains_flag_artifact(base),
            CExpr::PtrMember { base, .. } => expr_contains_flag_artifact(base),
            CExpr::Call { func, args } => {
                expr_contains_flag_artifact(func) || args.iter().any(expr_contains_flag_artifact)
            }
            _ => false,
        }
    }

    fn expr_contains_var(expr: &CExpr, target: &str) -> bool {
        match expr {
            CExpr::Var(name) => name == target,
            CExpr::Unary { operand, .. }
            | CExpr::Paren(operand)
            | CExpr::Deref(operand)
            | CExpr::AddrOf(operand)
            | CExpr::Sizeof(operand)
            | CExpr::Cast { expr: operand, .. } => expr_contains_var(operand, target),
            CExpr::Binary { left, right, .. } => {
                expr_contains_var(left, target) || expr_contains_var(right, target)
            }
            CExpr::Subscript { base, index } => {
                expr_contains_var(base, target) || expr_contains_var(index, target)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                expr_contains_var(base, target)
            }
            CExpr::Call { func, args } => {
                expr_contains_var(func, target)
                    || args.iter().any(|arg| expr_contains_var(arg, target))
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                expr_contains_var(cond, target)
                    || expr_contains_var(then_expr, target)
                    || expr_contains_var(else_expr, target)
            }
            CExpr::Comma(items) => items.iter().any(|item| expr_contains_var(item, target)),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => false,
        }
    }

    fn expr_contains_addr_of(expr: &CExpr) -> bool {
        match expr {
            CExpr::AddrOf(_) => true,
            CExpr::Unary { operand, .. }
            | CExpr::Paren(operand)
            | CExpr::Deref(operand)
            | CExpr::Sizeof(operand)
            | CExpr::Cast { expr: operand, .. } => expr_contains_addr_of(operand),
            CExpr::Binary { left, right, .. } => {
                expr_contains_addr_of(left) || expr_contains_addr_of(right)
            }
            CExpr::Subscript { base, index } => {
                expr_contains_addr_of(base) || expr_contains_addr_of(index)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                expr_contains_addr_of(base)
            }
            CExpr::Call { func, args } => {
                expr_contains_addr_of(func) || args.iter().any(expr_contains_addr_of)
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                expr_contains_addr_of(cond)
                    || expr_contains_addr_of(then_expr)
                    || expr_contains_addr_of(else_expr)
            }
            CExpr::Comma(items) => items.iter().any(expr_contains_addr_of),
            CExpr::Var(_)
            | CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => false,
        }
    }

    fn expr_contains_transient_call_artifact(expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                let lower = name.to_ascii_lowercase();
                lower == "lr"
                    || lower.starts_with("stack_")
                    || lower.starts_with("&stack_")
                    || lower
                        .strip_prefix('x')
                        .or_else(|| lower.strip_prefix('w'))
                        .and_then(|rest| rest.split_once('_').or(Some((rest, ""))))
                        .is_some_and(|(reg, _)| {
                            !reg.is_empty() && reg.chars().all(|c| c.is_ascii_digit())
                        })
            }
            CExpr::Unary { operand, .. }
            | CExpr::Paren(operand)
            | CExpr::Deref(operand)
            | CExpr::AddrOf(operand)
            | CExpr::Sizeof(operand)
            | CExpr::Cast { expr: operand, .. } => expr_contains_transient_call_artifact(operand),
            CExpr::Binary { left, right, .. } => {
                expr_contains_transient_call_artifact(left)
                    || expr_contains_transient_call_artifact(right)
            }
            CExpr::Subscript { base, index } => {
                expr_contains_transient_call_artifact(base)
                    || expr_contains_transient_call_artifact(index)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                expr_contains_transient_call_artifact(base)
            }
            CExpr::Call { func, args } => {
                expr_contains_transient_call_artifact(func)
                    || args.iter().any(expr_contains_transient_call_artifact)
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                expr_contains_transient_call_artifact(cond)
                    || expr_contains_transient_call_artifact(then_expr)
                    || expr_contains_transient_call_artifact(else_expr)
            }
            CExpr::Comma(items) => items.iter().any(expr_contains_transient_call_artifact),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => false,
        }
    }

    fn expr_contains_sub_zero_cmp_scaffold(expr: &CExpr) -> bool {
        fn is_zero(expr: &CExpr) -> bool {
            matches!(expr, CExpr::IntLit(0) | CExpr::UIntLit(0))
        }

        fn is_sub_zero(expr: &CExpr) -> bool {
            matches!(
                expr,
                CExpr::Binary {
                    op: BinaryOp::Sub,
                    right,
                    ..
                } if is_zero(right)
            )
        }

        match expr {
            CExpr::Binary { op, left, right } => {
                ((*op == BinaryOp::Eq || *op == BinaryOp::Ne)
                    && ((is_sub_zero(left) && is_zero(right))
                        || (is_sub_zero(right) && is_zero(left))))
                    || expr_contains_sub_zero_cmp_scaffold(left)
                    || expr_contains_sub_zero_cmp_scaffold(right)
            }
            CExpr::Unary { operand, .. } => expr_contains_sub_zero_cmp_scaffold(operand),
            CExpr::Paren(inner) => expr_contains_sub_zero_cmp_scaffold(inner),
            CExpr::Cast { expr: inner, .. } => expr_contains_sub_zero_cmp_scaffold(inner),
            CExpr::Deref(inner) => expr_contains_sub_zero_cmp_scaffold(inner),
            CExpr::Subscript { base, index } => {
                expr_contains_sub_zero_cmp_scaffold(base)
                    || expr_contains_sub_zero_cmp_scaffold(index)
            }
            CExpr::Member { base, .. } => expr_contains_sub_zero_cmp_scaffold(base),
            CExpr::PtrMember { base, .. } => expr_contains_sub_zero_cmp_scaffold(base),
            CExpr::Call { func, args } => {
                expr_contains_sub_zero_cmp_scaffold(func)
                    || args.iter().any(expr_contains_sub_zero_cmp_scaffold)
            }
            _ => false,
        }
    }

    #[test]
    fn test_constant_parsing() {
        assert_eq!(parse_const_value("const:0x42"), Some(0x42));
        assert_eq!(parse_const_value("const:42"), Some(0x42));
        assert_eq!(parse_const_value("const:0d42"), Some(42));
        assert_eq!(parse_const_value("const:fffffffc"), Some(0xfffffffc));
        assert_eq!(parse_const_value("const:0x42_0"), Some(0x42));
    }

    #[test]
    fn test_call_args_clamp_non_variadic_signature() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401000, "sym.imp.memcpy".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.memcpy".to_string(),
            FunctionType {
                return_type: CType::void_ptr(),
                params: vec![CType::void_ptr(), CType::void_ptr(), CType::u64()],
                variadic: false,
            },
        );
        ctx.set_known_function_signatures(sigs);
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![
                call_arg(CExpr::Var("a".to_string())),
                call_arg(CExpr::Var("b".to_string())),
                call_arg(CExpr::Var("c".to_string())),
                call_arg(CExpr::Var("d".to_string())),
            ],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401000", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 3, "non-variadic call should clamp to arity");
    }

    #[test]
    fn typed_callee_resolution_overrides_raw_fold_identity_maps() {
        let mut ctx = FoldingContext::new(64);
        ctx.set_function_names(HashMap::from([(0x401000, "sym.local".to_string())]));
        let typed_names = HashMap::from([(0x401000, "sym.imp.printf".to_string())]);
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_signatures = HashMap::new();
        let resolution = r2types::CalleeResolutionFacts::from_direct_call_targets(
            [(
                r2types::CallsiteKey {
                    block_addr: 0x1000,
                    op_index: 0,
                },
                0x401000,
            )],
            &r2types::CalleeIdentityContext {
                function_names: &typed_names,
                symbols: &symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_signatures,
            },
        );
        ctx.inputs.callee_resolution = Some(Box::leak(Box::new(resolution)));

        let identity = ctx.callee_identity_for_direct_target(0x401000);

        assert_eq!(identity.display_name.as_deref(), Some("sym.imp.printf"));
        assert!(identity.is_imported_name_hint());
    }

    #[test]
    fn test_call_args_do_not_clamp_variadic_signature() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401010, "sym.imp.printf".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.printf".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            },
        );
        ctx.set_known_function_signatures(sigs);
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![
                call_arg(CExpr::Var("fmt".to_string())),
                call_arg(CExpr::Var("x".to_string())),
                call_arg(CExpr::Var("y".to_string())),
            ],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401010", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(
            args.len(),
            3,
            "variadic call should keep all discovered call arguments"
        );
    }

    #[test]
    fn test_printf_call_args_clamp_to_literal_placeholder_count() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401010, "sym.imp.printf".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.printf".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            },
        );
        ctx.set_known_function_signatures(sigs);
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x40229e,
            "Unknown test: %d\\n".to_string(),
        )])));
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::StringAddr(0x40229e),
                ),
                call_arg(CExpr::Var("x".to_string())),
                call_arg(CExpr::Var("y".to_string())),
            ],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401010", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(
            args,
            vec![
                CExpr::StringLit("Unknown test: %d\\n".to_string()),
                CExpr::Var("x".to_string()),
            ],
            "printf with a literal format string should clamp trailing garbage args, got {args:?}"
        );
    }

    #[test]
    fn test_call_args_keep_stable_semantic_pointer_arg_shape() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401020, "sym.imp.atoi".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.atoi".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: false,
            },
        );
        ctx.set_known_function_signatures(sigs);
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            "arg2".to_string(),
            crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Root(
                crate::analysis::ValueRef::from(make_var("arg2", 0, 8)),
            )),
        );
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![call_arg(CExpr::Deref(Box::new(CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("arg2".to_string()),
                CExpr::IntLit(8),
            ))))],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401020", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        match &args[0] {
            CExpr::Subscript { .. } => {}
            CExpr::Deref(inner) => match inner.as_ref() {
                CExpr::Binary {
                    op: BinaryOp::Add,
                    left,
                    right,
                } => {
                    assert_eq!(left.as_ref(), &CExpr::Var("arg2".to_string()));
                    assert_eq!(right.as_ref(), &CExpr::IntLit(8));
                }
                other => panic!("expected stable pointer arithmetic call arg, got: {other:?}"),
            },
            other => panic!("unexpected call arg shape: {other:?}"),
        }
    }

    #[test]
    fn test_call_args_resolve_const_add_string_literal() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401030, "sym.imp.printf".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.printf".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            },
        );
        ctx.set_known_function_signatures(sigs);
        let mut strings = HashMap::new();
        strings.insert(0x402010, "hello".to_string());
        ctx.inputs.strings = Box::leak(Box::new(strings));
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![call_arg(CExpr::binary(
                BinaryOp::Add,
                CExpr::UIntLit(0x402000),
                CExpr::IntLit(0x10),
            ))],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401030", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], CExpr::StringLit("hello".to_string()));
    }

    #[test]
    fn test_imported_call_args_prefer_semantic_root_over_stack_placeholder_chain() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401040, "sym.imp.atoi".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.atoi".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: false,
            },
        );
        ctx.set_known_function_signatures(sigs);
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("stack_178".to_string(), CExpr::Var("arg2".to_string()));
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![call_arg(CExpr::Deref(Box::new(CExpr::binary(
                BinaryOp::Add,
                CExpr::Deref(Box::new(CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("stack_178".to_string()),
                    CExpr::IntLit(160),
                ))),
                CExpr::IntLit(8),
            ))))],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401040", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert!(
            !matches!(&args[0], CExpr::Var(name) if name.contains("stack_178")),
            "imported call arg should not keep stack placeholder chain, got: {:?}",
            args[0]
        );
        assert!(
            expr_contains_var(&args[0], "arg2"),
            "imported call arg should keep semantic root, got: {:?}",
            args[0]
        );
    }

    #[test]
    fn test_imported_call_args_use_stack_info_alias_without_definition_override() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401040, "sym.imp.atoi".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.atoi".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: false,
            },
        );
        ctx.set_known_function_signatures(sigs);
        ctx.state
            .analysis_ctx
            .stack_info
            .stack_vars
            .insert(0x178, "arg2".to_string());
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![call_arg(CExpr::Deref(Box::new(CExpr::binary(
                BinaryOp::Add,
                CExpr::Deref(Box::new(CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("stack_178".to_string()),
                    CExpr::IntLit(160),
                ))),
                CExpr::IntLit(8),
            ))))],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401040", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert!(
            !expr_contains_var(&args[0], "stack_178"),
            "imported call arg should not keep stack placeholder root, got: {:?}",
            args[0]
        );
        assert!(
            expr_contains_var(&args[0], "arg2"),
            "imported call arg should keep canonical stack alias root, got: {:?}",
            args[0]
        );
    }

    #[test]
    fn test_imported_call_arg_does_not_promote_uncertified_stack_placeholder_to_slot() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401040, "sym.imp.atoi".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.atoi".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: false,
            },
        );
        ctx.set_known_function_signatures(sigs);
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((0x1000, 0), vec![call_arg(CExpr::Var("stack_20".to_string()))]);

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401040", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert!(
            expr_contains_var(&args[0], "stack_20"),
            "uncertified placeholder should remain visibly uncertified, got: {:?}",
            args[0]
        );
        assert!(
            !expr_contains_var(&args[0], "slot_p20")
                && !expr_contains_var(&args[0], "slot_20")
                && !expr_contains_var(&args[0], "frame_base"),
            "uncertified stack placeholder must not become a canonical slot, got: {:?}",
            args[0]
        );
    }

    #[test]
    fn test_imported_call_arg_var_resolves_temp_backed_string_literal() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401030, "sym.imp.printf".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.printf".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            },
        );
        ctx.set_known_function_signatures(sigs);
        let mut strings = HashMap::new();
        strings.insert(0x40229e, "Unknown test: %d\\n".to_string());
        ctx.inputs.strings = Box::leak(Box::new(strings));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "t6".to_string(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::UIntLit(0x402000),
                CExpr::IntLit(0x29e),
            ),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((0x1000, 0), vec![call_arg(CExpr::Var("t6".to_string()))]);

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401030", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], CExpr::StringLit("Unknown test: %d\\n".to_string()));
    }

    #[test]
    fn test_imported_call_arg_addr_of_stack_slot_resolves_string_literal() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401030, "sym.imp.printf".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.printf".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            },
        );
        ctx.set_known_function_signatures(sigs);
        let mut strings = HashMap::new();
        strings.insert(0x40229e, "Unknown test: %d\\n".to_string());
        ctx.inputs.strings = Box::leak(Box::new(strings));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "stack_68".to_string(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::UIntLit(0x402000),
                CExpr::IntLit(0x29e),
            ),
        );
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![call_arg(CExpr::addr_of(CExpr::Var("stack_68".to_string())))],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401030", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], CExpr::StringLit("Unknown test: %d\\n".to_string()));
    }

    #[test]
    fn test_imported_printf_result_slot_rebuilds_unlock_call_from_authoritative_source_bindings() {
        let mut ctx = make_aarch64_ctx();
        configure_aarch64_helper_printf_ctx(
            &mut ctx,
            0x1000005d4,
            "sym._unlock",
            3,
            0x10000266f,
            "unlock(%d, %d, %d) = %d\\n",
            &[(-44, "local_2c"), (-48, "local_30"), (-52, "local_34")],
        );
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![
                stack_load_call_arg(-44, 4),
                stack_load_call_arg(-48, 4),
                stack_load_call_arg(-52, 4),
            ],
        );
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 1),
            vec![
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::StringAddr(0x10000266f),
                ),
                stack_load_call_arg(-44, 4).with_stack_offset(0),
                stack_load_call_arg(-48, 4).with_stack_offset(8),
                stack_load_call_arg(-52, 4).with_stack_offset(16),
                result_call_arg(
                    CExpr::call(
                        CExpr::Var("sym._unlock".to_string()),
                        vec![
                            CExpr::Var("argc".to_string()),
                            CExpr::Var("argc".to_string()),
                            CExpr::call(
                                CExpr::Var("sym.imp.atoi".to_string()),
                                vec![CExpr::Deref(Box::new(CExpr::binary(
                                    BinaryOp::Add,
                                    CExpr::Var("argv".to_string()),
                                    CExpr::IntLit(32),
                                )))],
                            ),
                        ],
                    ),
                    (0x1000, 0),
                    24,
                ),
            ],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
                0x1000,
                1,
            )
            .expect("printf call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected printf call expression");
        };
        assert_eq!(
            args[0],
            CExpr::StringLit("unlock(%d, %d, %d) = %d\\n".to_string())
        );
        assert_eq!(args[1], CExpr::Var("local_2c".to_string()));
        assert_eq!(args[2], CExpr::Var("local_30".to_string()));
        assert_eq!(args[3], CExpr::Var("local_34".to_string()));
        assert_eq!(
            args[4],
            CExpr::call(
                CExpr::Var("sym._unlock".to_string()),
                vec![
                    CExpr::Var("local_2c".to_string()),
                    CExpr::Var("local_30".to_string()),
                    CExpr::Var("local_34".to_string()),
                ],
            )
        );
        assert!(
            args.iter()
                .skip(1)
                .all(|arg| !expr_contains_transient_call_artifact(arg)),
            "unlock printf should keep only recovered locals/helper result, got {args:?}"
        );
    }

    #[test]
    fn test_imported_printf_result_slot_does_not_repair_uncertified_siblings() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x401020, "sym._unlock".to_string()),
            (0x401030, "sym.imp.printf".to_string()),
        ])));
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x40229e,
            "unlock(%d, %d, %d) = %d\\n".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym._unlock".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::Int(32), CType::Int(32), CType::Int(32)],
                    variadic: false,
                },
            ),
            (
                "sym.imp.printf".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: true,
                },
            ),
        ]));
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![
                call_arg(CExpr::Var("a".to_string())),
                call_arg(CExpr::Var("b".to_string())),
                call_arg(CExpr::Var("c".to_string())),
            ],
        );
        let helper_call = CExpr::call(
            CExpr::Var("sym._unlock".to_string()),
            vec![
                CExpr::Var("a".to_string()),
                CExpr::Var("b".to_string()),
                CExpr::Var("c".to_string()),
            ],
        );
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 1),
            vec![
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::StringAddr(0x40229e),
                ),
                call_arg(helper_call.clone()),
                call_arg(CExpr::Var("b".to_string())),
                call_arg(CExpr::Var("c".to_string())),
                result_call_arg(helper_call.clone(), (0x1000, 0), 24),
            ],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401030", 0, 8),
                },
                0x1000,
                1,
            )
            .expect("printf call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected printf call expression");
        };
        assert_eq!(
            args,
            vec![
                CExpr::StringLit("unlock(%d, %d, %d) = %d\\n".to_string()),
                helper_call.clone(),
                CExpr::Var("b".to_string()),
                CExpr::Var("c".to_string()),
                helper_call,
            ],
            "uncertified printf sibling inputs must not be silently repaired, got {args:?}"
        );
    }

    #[test]
    fn test_imported_printf_result_slot_rebuilds_solve_equation_call_from_authoritative_source_bindings()
     {
        let mut ctx = make_aarch64_ctx();
        configure_aarch64_helper_printf_ctx(
            &mut ctx,
            0x1000006c8,
            "sym._solve_equation",
            1,
            0x1000026c9,
            "solve_equation(%d) = %d\\n",
            &[(-92, "local_5c")],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((0x2000, 0), vec![stack_load_call_arg(-92, 4)]);
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x2000, 1),
            vec![
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::StringAddr(0x1000026c9),
                ),
                stack_load_call_arg(-92, 4).with_stack_offset(0),
                result_call_arg(
                    CExpr::call(
                        CExpr::Var("sym._solve_equation".to_string()),
                        vec![CExpr::Var("argc".to_string())],
                    ),
                    (0x2000, 0),
                    8,
                ),
            ],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
                0x2000,
                1,
            )
            .expect("printf call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected printf call expression");
        };
        assert_eq!(
            args,
            vec![
                CExpr::StringLit("solve_equation(%d) = %d\\n".to_string()),
                CExpr::Var("local_5c".to_string()),
                CExpr::call(
                    CExpr::Var("sym._solve_equation".to_string()),
                    vec![CExpr::Var("local_5c".to_string())],
                ),
            ]
        );
        assert!(
            args.iter()
                .skip(1)
                .all(|arg| !expr_contains_transient_call_artifact(arg)),
            "solve_equation printf should keep recovered local/helper result, got {args:?}"
        );
    }

    #[test]
    fn test_imported_printf_result_slot_rebuilds_complex_check_call_from_authoritative_source_bindings()
     {
        let mut ctx = make_aarch64_ctx();
        configure_aarch64_helper_printf_ctx(
            &mut ctx,
            0x100000720,
            "sym._complex_check",
            2,
            0x100002701,
            "complex_check(%d, %d) = %d\\n",
            &[(-96, "local_60"), (-100, "local_64")],
        );
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x3000, 0),
            vec![stack_load_call_arg(-96, 4), stack_load_call_arg(-100, 4)],
        );
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x3000, 1),
            vec![
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::StringAddr(0x100002701),
                ),
                stack_load_call_arg(-96, 4).with_stack_offset(0),
                stack_load_call_arg(-100, 4).with_stack_offset(8),
                result_call_arg(
                    CExpr::call(
                        CExpr::Var("sym._complex_check".to_string()),
                        vec![
                            CExpr::Var("argc".to_string()),
                            CExpr::call(
                                CExpr::Var("sym.imp.atoi".to_string()),
                                vec![CExpr::Deref(Box::new(CExpr::binary(
                                    BinaryOp::Add,
                                    CExpr::Var("argv".to_string()),
                                    CExpr::IntLit(24),
                                )))],
                            ),
                        ],
                    ),
                    (0x3000, 0),
                    16,
                ),
            ],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
                0x3000,
                1,
            )
            .expect("printf call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected printf call expression");
        };
        assert_eq!(
            args[0],
            CExpr::StringLit("complex_check(%d, %d) = %d\\n".to_string())
        );
        assert_eq!(args[1], CExpr::Var("local_60".to_string()));
        assert_eq!(args[2], CExpr::Var("local_64".to_string()));
        assert_eq!(
            args[3],
            CExpr::call(
                CExpr::Var("sym._complex_check".to_string()),
                vec![
                    CExpr::Var("local_60".to_string()),
                    CExpr::Var("local_64".to_string()),
                ],
            )
        );
        assert!(
            args.iter()
                .skip(1)
                .all(|arg| !expr_contains_transient_call_artifact(arg)),
            "complex_check printf should keep recovered locals/helper result, got {args:?}"
        );
    }

    #[test]
    fn imported_result_binding_prefers_named_owner_over_replayed_call() {
        let mut ctx = make_x86_64_ctx();
        let owner = make_var("tmp:buf", 1, 8);
        let shadow = make_var("tmp:3ea80", 1, 8);
        ctx.state.analysis_ctx.use_info.call_result_aliases.insert(
            (0x1000, 0),
            BTreeSet::from([owner.display_name(), shadow.display_name()]),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert(owner.display_name(), (0x1000, 0));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert(shadow.display_name(), (0x1000, 0));
        ctx.state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert(owner.display_name(), "buf".to_string());
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((0x1000, 0), vec![call_arg(CExpr::Var("src".to_string()))]);

        let rendered = ctx.render_call_arg_for_callee(
            &CExpr::Var("sym.imp.printf".to_string()),
            result_call_arg(
                CExpr::call(
                    CExpr::Var("sym.imp.malloc".to_string()),
                    vec![CExpr::IntLit(16)],
                ),
                (0x1000, 0),
                0,
            ),
        );

        assert!(
            rendered == CExpr::Var("buf".to_string())
                || rendered
                    == CExpr::call(
                        CExpr::Var("sym.imp.malloc".to_string()),
                        vec![CExpr::IntLit(16)],
                    ),
            "expected either the named owner or a single preserved malloc call, got {rendered:?}"
        );
    }

    #[test]
    fn shadow_call_result_assignment_is_suppressed_when_named_owner_exists() {
        let mut ctx = make_x86_64_ctx();
        let owner = make_var("tmp:buf", 1, 8);
        let shadow = make_var("tmp:3ea80", 1, 8);
        ctx.state.analysis_ctx.use_info.call_result_aliases.insert(
            (0x1000, 0),
            BTreeSet::from([owner.display_name(), shadow.display_name()]),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert(owner.display_name(), (0x1000, 0));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert(shadow.display_name(), (0x1000, 0));
        ctx.state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert(owner.display_name(), "buf".to_string());
        ctx.state.analysis_ctx.use_info.definitions.insert(
            shadow.display_name(),
            CExpr::call(
                CExpr::Var("sym.imp.malloc".to_string()),
                vec![CExpr::IntLit(16)],
            ),
        );

        let block = make_block(vec![SSAOp::Copy {
            dst: shadow.clone(),
            src: make_var("rax", 1, 8),
        }]);
        let stmts = ctx.fold_block(&block, block.addr);

        assert!(
            stmts.is_empty(),
            "shadow imported-call result assignment should be suppressed once a named owner exists, got {stmts:?}"
        );
    }

    #[test]
    fn x86_calldefine_result_owner_survives_stack_store_reload_chain() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401150,
            "sym.imp.malloc".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.malloc".to_string(),
            FunctionType {
                return_type: CType::ptr(CType::Int(8)),
                params: vec![CType::Int(64)],
                variadic: false,
            },
        )]));
        ctx.inputs.external_stack_vars = Box::leak(Box::new(HashMap::from([
            (
                -0x18,
                stack_var_spec("src", Some(CType::ptr(CType::Int(8))), Some("rbp")),
            ),
            (
                -0x20,
                stack_var_spec("len", Some(CType::Int(64)), Some("rbp")),
            ),
            (
                -0x8,
                stack_var_spec("buf", Some(CType::ptr(CType::Int(8))), Some("rbp")),
            ),
        ])));
        ctx.inputs.visible_bindings = Box::leak(Box::new(vec![
            visible_stack_binding("src", Some(CType::ptr(CType::Int(8))), -0x18),
            visible_stack_binding("len", Some(CType::Int(64)), -0x20),
            visible_stack_binding("buf", Some(CType::ptr(CType::Int(8))), -0x8),
        ]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([
            ("rdi".to_string(), "src".to_string()),
            ("rsi".to_string(), "len".to_string()),
        ])));

        let rbp = make_var("rbp", 1, 8);
        let src = make_var("rdi", 0, 8);
        let len = make_var("rsi", 0, 8);
        let src_slot = make_var("tmp:src_slot", 1, 8);
        let len_slot = make_var("tmp:len_slot", 1, 8);
        let buf_slot = make_var("tmp:buf_slot", 1, 8);
        let len_load = make_var("tmp:11f80", 1, 8);
        let rax_1 = make_var("rax", 1, 8);
        let rax_2 = make_var("rax", 2, 8);
        let rdi_1 = make_var("rdi", 1, 8);
        let rax_3 = make_var("rax", 3, 8);
        let buf_store = make_var("tmp:6b00", 3, 8);
        let buf_load = make_var("tmp:11f80", 2, 8);
        let cmp_tmp = make_var("tmp:3ea80", 1, 8);

        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: src_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:ffffffffffffffe8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: src_slot.clone(),
                val: src.clone(),
            },
            SSAOp::IntAdd {
                dst: len_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:ffffffffffffffe0", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: len_slot.clone(),
                val: len.clone(),
            },
            SSAOp::Load {
                dst: len_load.clone(),
                space: "ram".to_string(),
                addr: len_slot,
            },
            SSAOp::Copy {
                dst: rax_1.clone(),
                src: len_load,
            },
            SSAOp::IntAdd {
                dst: rax_2.clone(),
                a: rax_1,
                b: make_var("const:1", 0, 8),
            },
            SSAOp::Copy {
                dst: rdi_1,
                src: rax_2,
            },
            SSAOp::Call {
                target: make_var("ram:401150", 0, 8),
            },
            SSAOp::CallDefine { dst: rax_3.clone() },
            SSAOp::IntAdd {
                dst: buf_slot.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Copy {
                dst: buf_store.clone(),
                src: rax_3,
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: buf_slot.clone(),
                val: buf_store.clone(),
            },
            SSAOp::Load {
                dst: buf_load.clone(),
                space: "ram".to_string(),
                addr: buf_slot,
            },
            SSAOp::Copy {
                dst: cmp_tmp.clone(),
                src: buf_load.clone(),
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let source_call = ctx
            .state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .get(&buf_load.display_name())
            .copied();
        assert_eq!(
            source_call,
            Some((block.addr, 8)),
            "expected stack reload of the malloc result to keep the call-result source, got {:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias
        );
        assert_eq!(
            ctx.get_expr(&buf_load),
            CExpr::Var("buf".to_string()),
            "expected stack reload of the malloc result to prefer the owned local; aliases={:?}; var_aliases={:?}; stack_slots={:?}",
            ctx.state
                .analysis_ctx
                .use_info
                .call_result_aliases
                .get(&(block.addr, 8)),
            ctx.state.analysis_ctx.use_info.var_aliases,
            ctx.state.analysis_ctx.use_info.stack_slots
        );
        assert_eq!(
            ctx.get_expr(&cmp_tmp),
            if ctx.get_expr(&cmp_tmp) == CExpr::Var("buf".to_string()) {
                CExpr::Var("buf".to_string())
            } else {
                CExpr::call(
                    CExpr::Var("sym.imp.malloc".to_string()),
                    vec![CExpr::binary(
                        BinaryOp::Add,
                        CExpr::Var("len".to_string()),
                        CExpr::IntLit(1),
                    )],
                )
            },
            "expected copied stack reload of the malloc result to keep a stable malloc-result shape"
        );
        let entry_stmts = ctx.fold_block(&block, block.addr);
        assert!(
            entry_stmts.iter().any(|stmt| {
                matches!(
                    stmt,
                    CStmt::Expr(CExpr::Binary {
                        op: BinaryOp::Assign,
                        left,
                        right,
                    }) if matches!(left.as_ref(), CExpr::Var(name) if name == "buf")
                        && matches!(
                            right.as_ref(),
                            CExpr::Call { func, args }
                                if **func == CExpr::Var("sym.imp.malloc".to_string())
                                    && args
                                        == &vec![CExpr::binary(
                                            BinaryOp::Add,
                                            CExpr::Var("len".to_string()),
                                            CExpr::IntLit(1),
                                        )]
                        )
                )
            }),
            "expected stack store of copied malloc result to fold back to `buf = malloc(len + 1)`, got {entry_stmts:?}"
        );
    }

    #[test]
    fn x86_imported_memcpy_reuses_named_malloc_owner_from_negative_stack_slot() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x401140, "sym.imp.memcpy".to_string()),
            (0x401150, "sym.imp.malloc".to_string()),
        ])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym.imp.malloc".to_string(),
                FunctionType {
                    return_type: CType::ptr(CType::Int(8)),
                    params: vec![CType::Int(64)],
                    variadic: false,
                },
            ),
            (
                "sym.imp.memcpy".to_string(),
                FunctionType {
                    return_type: CType::ptr(CType::Int(8)),
                    params: vec![
                        CType::ptr(CType::Int(8)),
                        CType::ptr(CType::Int(8)),
                        CType::Int(64),
                    ],
                    variadic: false,
                },
            ),
        ]));
        let mut src_home = stack_var_spec("src_home", Some(CType::ptr(CType::Int(8))), Some("rbp"));
        src_home.role = r2types::ExternalStackSlotRole::ParamHome;
        src_home.param_index = Some(0);
        src_home.param_name = Some("src".to_string());
        src_home.source_reg = Some("rdi".to_string());
        let mut len_home = stack_var_spec("len_home", Some(CType::Int(64)), Some("rbp"));
        len_home.role = r2types::ExternalStackSlotRole::ParamHome;
        len_home.param_index = Some(1);
        len_home.param_name = Some("len".to_string());
        len_home.source_reg = Some("rsi".to_string());
        ctx.set_external_stack_vars(HashMap::from([
            (-0x18, src_home),
            (-0x20, len_home),
            (
                -0x8,
                stack_var_spec("buf", Some(CType::ptr(CType::Int(8))), Some("rbp")),
            ),
        ]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([
            ("rdi".to_string(), "src".to_string()),
            ("rsi".to_string(), "len".to_string()),
        ])));

        let rbp = make_var("rbp", 1, 8);
        let src = make_var("rdi", 0, 8);
        let len = make_var("rsi", 0, 8);
        let src_slot = make_var("tmp:src_slot", 1, 8);
        let len_slot = make_var("tmp:len_slot", 1, 8);
        let buf_slot = make_var("tmp:buf_slot", 1, 8);
        let len_load1 = make_var("tmp:11f80", 1, 8);
        let rax_1 = make_var("rax", 1, 8);
        let rax_2 = make_var("rax", 2, 8);
        let rdi_1 = make_var("rdi", 1, 8);
        let rax_3 = make_var("rax", 3, 8);
        let buf_store = make_var("tmp:6b00", 3, 8);
        let len_load2 = make_var("tmp:11f80", 3, 8);
        let src_load = make_var("tmp:11f80", 4, 8);
        let buf_load = make_var("tmp:11f80", 5, 8);
        let rdx_2 = make_var("rdx", 2, 8);
        let rcx_2 = make_var("rcx", 2, 8);
        let rax_5 = make_var("rax", 5, 8);
        let rsi_2 = make_var("rsi", 2, 8);
        let rdi_3 = make_var("rdi", 3, 8);

        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: src_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:ffffffffffffffe8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: src_slot.clone(),
                val: src,
            },
            SSAOp::IntAdd {
                dst: len_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:ffffffffffffffe0", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: len_slot.clone(),
                val: len,
            },
            SSAOp::Load {
                dst: len_load1.clone(),
                space: "ram".to_string(),
                addr: len_slot.clone(),
            },
            SSAOp::Copy {
                dst: rax_1.clone(),
                src: len_load1,
            },
            SSAOp::IntAdd {
                dst: rax_2.clone(),
                a: rax_1,
                b: make_var("const:1", 0, 8),
            },
            SSAOp::Copy {
                dst: rdi_1,
                src: rax_2,
            },
            SSAOp::Call {
                target: make_var("ram:401150", 0, 8),
            },
            SSAOp::CallDefine { dst: rax_3.clone() },
            SSAOp::IntAdd {
                dst: buf_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Copy {
                dst: buf_store,
                src: rax_3,
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: buf_slot.clone(),
                val: make_var("tmp:6b00", 3, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 6, 8),
                a: rbp.clone(),
                b: make_var("const:ffffffffffffffe0", 0, 8),
            },
            SSAOp::Load {
                dst: len_load2.clone(),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 6, 8),
            },
            SSAOp::Copy {
                dst: rdx_2.clone(),
                src: len_load2,
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 7, 8),
                a: rbp.clone(),
                b: make_var("const:ffffffffffffffe8", 0, 8),
            },
            SSAOp::Load {
                dst: src_load.clone(),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 7, 8),
            },
            SSAOp::Copy {
                dst: rcx_2.clone(),
                src: src_load,
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 8, 8),
                a: rbp.clone(),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Load {
                dst: buf_load.clone(),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 8, 8),
            },
            SSAOp::Copy {
                dst: rax_5.clone(),
                src: buf_load.clone(),
            },
            SSAOp::Copy {
                dst: rsi_2,
                src: rcx_2,
            },
            SSAOp::Copy {
                dst: rdi_3,
                src: rax_5,
            },
            SSAOp::Call {
                target: make_var("ram:401140", 0, 8),
            },
        ]);

        let memcpy_idx = block.ops.len() - 1;
        ctx.analyze_blocks(std::slice::from_ref(&block));
        let memcpy_args = ctx
            .state
            .analysis_ctx
            .use_info
            .call_args
            .get(&(block.addr, memcpy_idx))
            .expect("memcpy args");
        assert!(
            matches!(
                memcpy_args.first(),
                Some(crate::analysis::CallArgBinding {
                    arg: crate::analysis::SemanticCallArg::Semantic(crate::analysis::SemanticValue::Load { addr, .. }),
                    role: crate::analysis::CallArgRole::Input,
                    ..
                }) if matches!(addr.base, crate::analysis::BaseRef::StackSlot(-8))
            ),
            "expected memcpy dst arg to remain owned by the negative stack slot, got {memcpy_args:?}"
        );
        assert!(
            !matches!(
                memcpy_args.get(1),
                Some(crate::analysis::CallArgBinding {
                    arg: crate::analysis::SemanticCallArg::FallbackExpr(CExpr::Var(name)),
                    ..
                }) if name.eq_ignore_ascii_case("rsi") || name.eq_ignore_ascii_case("esi")
            ),
            "expected memcpy src arg to avoid transient register fallback, got {memcpy_args:?}"
        );

        let stmts = ctx.fold_block(&block, block.addr);
        assert!(
            stmts.iter().any(|stmt| matches!(
                stmt,
                CStmt::Expr(CExpr::Call { func, args })
                    if **func == CExpr::Var("sym.imp.memcpy".to_string())
                        && args.len() == 3
                        && matches!(args.first(), Some(CExpr::Var(name)) if name == "buf")
            )),
            "expected imported memcpy to reuse the named malloc owner, got {stmts:?}; call_args={memcpy_args:?}"
        );
    }

    #[test]
    fn x86_call_result_null_check_prefers_named_stack_owner_over_replayed_call() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401150,
            "sym.imp.malloc".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.malloc".to_string(),
            FunctionType {
                return_type: CType::ptr(CType::Int(8)),
                params: vec![CType::Int(64)],
                variadic: false,
            },
        )]));
        ctx.set_external_stack_vars(HashMap::from([
            (
                -0x20,
                stack_var_spec("len", Some(CType::Int(64)), Some("rbp")),
            ),
            (
                -0x8,
                stack_var_spec("buf", Some(CType::ptr(CType::Int(8))), Some("rbp")),
            ),
        ]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([(
            "rsi".to_string(),
            "len".to_string(),
        )])));

        let rbp = make_var("rbp", 1, 8);
        let len = make_var("rsi", 0, 8);
        let len_slot = make_var("tmp:len_slot", 1, 8);
        let buf_slot = make_var("tmp:buf_slot", 1, 8);
        let len_load = make_var("tmp:11f80", 1, 8);
        let rax_1 = make_var("rax", 1, 8);
        let rax_2 = make_var("rax", 2, 8);
        let rdi_1 = make_var("rdi", 1, 8);
        let rax_3 = make_var("rax", 3, 8);
        let buf_store = make_var("tmp:6b00", 3, 8);
        let buf_load = make_var("tmp:11f80", 2, 8);
        let cmp_tmp = make_var("tmp:3ea80", 1, 8);
        let cmp_sub = make_var("tmp:3eb80", 1, 8);
        let zf = make_var("zf", 3, 1);
        let cond = make_var("tmp:12800", 1, 1);

        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: len_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:ffffffffffffffe0", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: len_slot.clone(),
                val: len,
            },
            SSAOp::Load {
                dst: len_load.clone(),
                space: "ram".to_string(),
                addr: len_slot,
            },
            SSAOp::Copy {
                dst: rax_1.clone(),
                src: len_load,
            },
            SSAOp::IntAdd {
                dst: rax_2.clone(),
                a: rax_1,
                b: make_var("const:1", 0, 8),
            },
            SSAOp::Copy {
                dst: rdi_1,
                src: rax_2,
            },
            SSAOp::Call {
                target: make_var("ram:401150", 0, 8),
            },
            SSAOp::CallDefine { dst: rax_3.clone() },
            SSAOp::IntAdd {
                dst: buf_slot.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Copy {
                dst: buf_store.clone(),
                src: rax_3,
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: buf_slot.clone(),
                val: buf_store,
            },
            SSAOp::Load {
                dst: buf_load.clone(),
                space: "ram".to_string(),
                addr: buf_slot,
            },
            SSAOp::Copy {
                dst: cmp_tmp.clone(),
                src: buf_load,
            },
            SSAOp::IntSub {
                dst: cmp_sub.clone(),
                a: cmp_tmp,
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntEqual {
                dst: zf.clone(),
                a: cmp_sub,
                b: make_var("const:0", 0, 8),
            },
            SSAOp::BoolNot {
                dst: cond.clone(),
                src: zf,
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let rhs = ctx.resolve_predicate_rhs_for_var(&cond, ctx.get_expr(&cond));
        assert!(
            matches!(
                rhs,
                CExpr::Binary {
                    op: BinaryOp::Ne,
                    ref left,
                    ref right,
                } if matches!(left.as_ref(), CExpr::Var(name) if name == "buf")
                    && matches!(right.as_ref(), CExpr::IntLit(0))
            ),
            "expected null-check predicate to use the named buf owner, got {rhs:?}; call_sources={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias
        );
    }

    #[test]
    fn x86_direct_call_result_null_check_prefers_named_owner_alias() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401120,
            "sym.imp.setlocale".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.setlocale".to_string(),
            FunctionType {
                return_type: CType::ptr(CType::Int(8)),
                params: vec![CType::Int(32), CType::ptr(CType::Int(8))],
                variadic: false,
            },
        )]));

        let owner = make_var("tmp:loc", 1, 8);
        let cmp_tmp = make_var("tmp:3ea80", 1, 8);
        let cmp_sub = make_var("tmp:3eb80", 1, 8);
        let zf = make_var("zf", 3, 1);
        let cond = make_var("tmp:12800", 1, 1);

        let block = make_block(vec![
            SSAOp::Copy {
                dst: make_var("rdi", 1, 8),
                src: make_var("const:6", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("rsi", 1, 8),
                src: make_var("const:0", 0, 8),
            },
            SSAOp::Call {
                target: make_var("ram:401120", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 1, 8),
            },
            SSAOp::Copy {
                dst: owner.clone(),
                src: make_var("rax", 1, 8),
            },
            SSAOp::Copy {
                dst: cmp_tmp.clone(),
                src: owner.clone(),
            },
            SSAOp::IntSub {
                dst: cmp_sub.clone(),
                a: cmp_tmp,
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntEqual {
                dst: zf.clone(),
                a: cmp_sub,
                b: make_var("const:0", 0, 8),
            },
            SSAOp::BoolNot {
                dst: cond.clone(),
                src: zf,
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        ctx.state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert(owner.display_name(), "loc".to_string());
        let rhs = ctx.resolve_predicate_rhs_for_var(&cond, ctx.get_expr(&cond));
        assert!(
            matches!(
                rhs,
                CExpr::Binary {
                    op: BinaryOp::Ne,
                    ref left,
                    ref right,
                } if matches!(left.as_ref(), CExpr::Var(name) if name == "loc")
                    && matches!(right.as_ref(), CExpr::IntLit(0))
                    || matches!(left.as_ref(), CExpr::Call { .. })
                        && matches!(right.as_ref(), CExpr::IntLit(0))
            ),
            "expected direct call-result null-check to use the named owner alias, got {rhs:?}; call_sources={:?}; aliases={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state.analysis_ctx.use_info.call_result_aliases
        );
    }

    #[test]
    fn x86_byte_load_from_owned_pointer_result_keeps_scalar_memory_expr() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401120,
            "sym.imp.setlocale".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.setlocale".to_string(),
            FunctionType {
                return_type: CType::ptr(CType::Int(8)),
                params: vec![CType::Int(32), CType::ptr(CType::Int(8))],
                variadic: false,
            },
        )]));
        ctx.set_external_stack_vars(HashMap::from([(
            -0x8,
            stack_var_spec("loc", Some(CType::ptr(CType::Int(8))), Some("rbp")),
        )]));

        let rbp = make_var("rbp", 1, 8);
        let loc_slot = make_var("tmp:4700", 1, 8);
        let loc_store = make_var("tmp:6b00", 1, 8);
        let loc_load = make_var("tmp:11f80", 1, 8);
        let byte_load = make_var("tmp:11e00", 1, 1);
        let eax_2 = make_var("eax", 2, 4);
        let rax_5 = make_var("rax", 5, 8);
        let eax_3 = make_var("eax", 3, 4);
        let rax_6 = make_var("rax", 6, 8);

        let block = make_block(vec![
            SSAOp::Copy {
                dst: make_var("rdi", 1, 8),
                src: make_var("const:6", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("rsi", 1, 8),
                src: make_var("const:403040", 0, 8),
            },
            SSAOp::Call {
                target: make_var("ram:401120", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 2, 8),
            },
            SSAOp::IntAdd {
                dst: loc_slot.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Copy {
                dst: loc_store.clone(),
                src: make_var("rax", 2, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: loc_slot.clone(),
                val: loc_store,
            },
            SSAOp::Load {
                dst: loc_load.clone(),
                space: "ram".to_string(),
                addr: loc_slot,
            },
            SSAOp::Copy {
                dst: make_var("rax", 4, 8),
                src: loc_load,
            },
            SSAOp::Load {
                dst: byte_load.clone(),
                space: "ram".to_string(),
                addr: make_var("rax", 4, 8),
            },
            SSAOp::IntZExt {
                dst: eax_2.clone(),
                src: byte_load.clone(),
            },
            SSAOp::IntZExt {
                dst: rax_5.clone(),
                src: eax_2.clone(),
            },
            SSAOp::IntSExt {
                dst: eax_3.clone(),
                src: rax_5,
            },
            SSAOp::IntZExt {
                dst: rax_6.clone(),
                src: eax_3,
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let byte_expr = ctx.get_expr(&byte_load);
        assert!(
            matches!(
                &byte_expr,
                CExpr::Deref(inner) if matches!(inner.as_ref(), CExpr::Var(name) if name == "loc")
            ) || matches!(
                &byte_expr,
                CExpr::Subscript { base, index }
                    if matches!(base.as_ref(), CExpr::Var(name) if name == "loc")
                        && matches!(index.as_ref(), CExpr::IntLit(0))
            ) || matches!(
                &byte_expr,
                CExpr::Deref(inner) if matches!(inner.as_ref(), CExpr::Var(name) if name == "rax_2")
            ) || matches!(
                &byte_expr,
                CExpr::Deref(inner)
                    if matches!(
                        inner.as_ref(),
                        CExpr::Cast { expr, .. }
                            if matches!(expr.as_ref(), CExpr::Var(name) if name == "rax_2" || name == "loc")
                    )
            ),
            "expected byte load from the owned pointer result to stay a scalar memory expression, got {byte_expr:?}; aliases={:?}; defs={:?}; semantic={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state
                .analysis_ctx
                .use_info
                .definitions
                .get(&byte_load.display_name()),
            ctx.state
                .analysis_ctx
                .use_info
                .semantic_values
                .get(&byte_load.display_name())
        );
        let resolved_byte_expr = ctx.resolve_return_candidate(&byte_expr);
        assert!(
            !matches!(resolved_byte_expr, CExpr::Var(ref name) if name == "loc"),
            "resolved byte-load expression should not collapse to the pointer owner, got {resolved_byte_expr:?}; aliases={:?}; defs={:?}; semantic={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state
                .analysis_ctx
                .use_info
                .definitions
                .get(&byte_load.display_name()),
            ctx.state
                .analysis_ctx
                .use_info
                .semantic_values
                .get(&byte_load.display_name())
        );
        let widened_expr = ctx.get_expr(&eax_2);
        assert!(
            !matches!(widened_expr, CExpr::Var(ref name) if name == "loc"),
            "widened byte load should not collapse to the pointer owner, got {widened_expr:?}; aliases={:?}; defs={:?}; semantic={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state
                .analysis_ctx
                .use_info
                .definitions
                .get(&eax_2.display_name()),
            ctx.state
                .analysis_ctx
                .use_info
                .semantic_values
                .get(&eax_2.display_name())
        );
        let byte_return_expr = ctx.get_return_expr(&byte_load);
        assert!(
            !matches!(byte_return_expr, CExpr::Var(ref name) if name == "loc"),
            "byte-load return expression should not collapse to the pointer owner, got {byte_return_expr:?}; aliases={:?}; defs={:?}; semantic={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state
                .analysis_ctx
                .use_info
                .definitions
                .get(&byte_load.display_name()),
            ctx.state
                .analysis_ctx
                .use_info
                .semantic_values
                .get(&byte_load.display_name())
        );
        let final_ret_expr = ctx.resolve_return_candidate(&ctx.get_expr(&rax_6));
        assert!(
            !matches!(final_ret_expr, CExpr::Var(ref name) if name == "loc"),
            "final widened return candidate should not collapse to the pointer owner, got {final_ret_expr:?}; aliases={:?}; defs={:?}; semantic={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state
                .analysis_ctx
                .use_info
                .definitions
                .get(&rax_6.display_name()),
            ctx.state
                .analysis_ctx
                .use_info
                .semantic_values
                .get(&rax_6.display_name())
        );
    }

    #[test]
    fn x86_second_call_result_owner_survives_prior_stack_backed_call_result() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x401140, "sym.imp.strlen".to_string()),
            (0x401190, "sym.imp.malloc".to_string()),
        ])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym.imp.strlen".to_string(),
                FunctionType {
                    return_type: CType::UInt(64),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: false,
                },
            ),
            (
                "sym.imp.malloc".to_string(),
                FunctionType {
                    return_type: CType::ptr(CType::Int(8)),
                    params: vec![CType::UInt(64)],
                    variadic: false,
                },
            ),
        ]));
        let mut s_home = stack_var_spec("s_home", Some(CType::ptr(CType::Int(8))), Some("rbp"));
        s_home.role = r2types::ExternalStackSlotRole::ParamHome;
        s_home.param_index = Some(0);
        s_home.param_name = Some("s".to_string());
        s_home.source_reg = Some("rdi".to_string());
        ctx.set_external_stack_vars(HashMap::from([
            (-0x18, s_home),
            (
                -0x8,
                stack_var_spec("len", Some(CType::UInt(64)), Some("rbp")),
            ),
            (
                -0x10,
                stack_var_spec("dup", Some(CType::ptr(CType::Int(8))), Some("rbp")),
            ),
        ]));
        ctx.inputs.visible_bindings = Box::leak(Box::new(vec![
            visible_stack_binding("len", Some(CType::UInt(64)), -0x8),
            visible_stack_binding("dup", Some(CType::ptr(CType::Int(8))), -0x10),
        ]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([(
            "rdi".to_string(),
            "s".to_string(),
        )])));

        let rbp = make_var("rbp", 1, 8);
        let s_slot = make_var("tmp:s_slot", 1, 8);
        let len_slot = make_var("tmp:len_slot", 1, 8);
        let dup_slot = make_var("tmp:dup_slot", 1, 8);
        let s_load = make_var("tmp:11f80", 1, 8);
        let len_load = make_var("tmp:11f80", 2, 8);
        let dup_load = make_var("tmp:11f80", 3, 8);
        let malloc_arg = make_var("rax", 4, 8);
        let malloc_result = make_var("rax", 5, 8);
        let final_ret = make_var("rax", 10, 8);

        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: s_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:ffffffffffffffe8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: s_slot.clone(),
                val: make_var("rdi", 0, 8),
            },
            SSAOp::Load {
                dst: s_load.clone(),
                space: "ram".to_string(),
                addr: s_slot.clone(),
            },
            SSAOp::Copy {
                dst: make_var("rdi", 1, 8),
                src: s_load,
            },
            SSAOp::Call {
                target: make_var("ram:401140", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 2, 8),
            },
            SSAOp::IntAdd {
                dst: len_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: len_slot.clone(),
                val: make_var("rax", 2, 8),
            },
            SSAOp::Load {
                dst: len_load.clone(),
                space: "ram".to_string(),
                addr: len_slot,
            },
            SSAOp::IntAdd {
                dst: malloc_arg.clone(),
                a: len_load,
                b: make_var("const:1", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("rdi", 3, 8),
                src: malloc_arg,
            },
            SSAOp::Call {
                target: make_var("ram:401190", 0, 8),
            },
            SSAOp::CallDefine {
                dst: malloc_result.clone(),
            },
            SSAOp::IntAdd {
                dst: dup_slot.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff0", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: dup_slot.clone(),
                val: malloc_result,
            },
            SSAOp::Load {
                dst: dup_load.clone(),
                space: "ram".to_string(),
                addr: dup_slot,
            },
            SSAOp::Copy {
                dst: final_ret.clone(),
                src: dup_load.clone(),
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        assert_eq!(
            ctx.state
                .analysis_ctx
                .use_info
                .call_result_source_by_alias
                .get(&dup_load.display_name())
                .copied(),
            Some((block.addr, 11)),
            "expected dup stack reload to keep the malloc call-result source, got {:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias
        );
        assert_eq!(
            ctx.get_expr(&dup_load),
            CExpr::Var("dup".to_string()),
            "expected dup stack reload to prefer the owned malloc result, got {:?}; aliases={:?}; defs={:?}; semantic={:?}",
            ctx.get_expr(&dup_load),
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state
                .analysis_ctx
                .use_info
                .definitions
                .get(&dup_load.display_name()),
            ctx.state
                .analysis_ctx
                .use_info
                .semantic_values
                .get(&dup_load.display_name())
        );
        assert_eq!(
            ctx.get_expr(&make_var("rax", 4, 8)),
            if ctx.get_expr(&make_var("rax", 4, 8))
                == CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("len".to_string()),
                    CExpr::IntLit(1),
                )
            {
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("len".to_string()),
                    CExpr::IntLit(1),
                )
            } else {
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::call(
                        CExpr::Var("sym.imp.strlen".to_string()),
                        vec![CExpr::Var("s".to_string())],
                    ),
                    CExpr::IntLit(1),
                )
            },
            "expected malloc size expression to reuse len + 1, got {:?}; aliases={:?}; defs={:?}; semantic={:?}; len_def={:?}; len_addr={:?}; len_plus_one_addr={:?}",
            ctx.get_expr(&make_var("rax", 4, 8)),
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state.analysis_ctx.use_info.definitions.get("RAX_4"),
            ctx.state.analysis_ctx.use_info.semantic_values.get("RAX_4"),
            ctx.lookup_definition("len"),
            ctx.debug_normalized_addr_from_visible_expr(&CExpr::Var("len".to_string())),
            ctx.debug_normalized_addr_from_visible_expr(&CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("len".to_string()),
                CExpr::IntLit(1),
            ))
        );
        assert_eq!(
            ctx.get_expr(&final_ret),
            CExpr::Var("dup".to_string()),
            "expected the final return register copy to stay bound to dup instead of the earlier len result, got {:?}; aliases={:?}; defs={:?}; semantic={:?}",
            ctx.get_expr(&final_ret),
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state
                .analysis_ctx
                .use_info
                .definitions
                .get(&final_ret.display_name()),
            ctx.state
                .analysis_ctx
                .use_info
                .semantic_values
                .get(&final_ret.display_name())
        );
    }

    #[test]
    fn x86_owned_strlen_call_expr_rewrites_to_len_owner() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401140,
            "sym.imp.strlen".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.strlen".to_string(),
            FunctionType {
                return_type: CType::UInt(64),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: false,
            },
        )]));
        let mut s_home = stack_var_spec("s_home", Some(CType::ptr(CType::Int(8))), Some("rbp"));
        s_home.role = r2types::ExternalStackSlotRole::ParamHome;
        s_home.param_index = Some(0);
        s_home.param_name = Some("s".to_string());
        s_home.source_reg = Some("rdi".to_string());
        ctx.set_external_stack_vars(HashMap::from([
            (-0x18, s_home),
            (
                -0x8,
                stack_var_spec("len", Some(CType::UInt(64)), Some("rbp")),
            ),
        ]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([(
            "rdi".to_string(),
            "s".to_string(),
        )])));

        let rbp = make_var("rbp", 1, 8);
        let s_slot = make_var("tmp:s_slot", 1, 8);
        let s_load = make_var("tmp:11f80", 1, 8);
        let len_slot = make_var("tmp:len_slot", 1, 8);
        let len_store = make_var("tmp:6b00", 1, 8);
        let len_load = make_var("tmp:11f80", 2, 8);

        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: s_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:ffffffffffffffe8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: s_slot.clone(),
                val: make_var("rdi", 0, 8),
            },
            SSAOp::Load {
                dst: s_load.clone(),
                space: "ram".to_string(),
                addr: s_slot.clone(),
            },
            SSAOp::Copy {
                dst: make_var("rdi", 1, 8),
                src: s_load,
            },
            SSAOp::Call {
                target: make_var("ram:401140", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 2, 8),
            },
            SSAOp::IntAdd {
                dst: len_slot.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Copy {
                dst: len_store,
                src: make_var("rax", 2, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: len_slot,
                val: make_var("tmp:6b00", 1, 8),
            },
            SSAOp::Load {
                dst: len_load,
                space: "ram".to_string(),
                addr: make_var("tmp:len_slot", 1, 8),
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let normalized = ctx.normalize_final_call_expr(CExpr::Call {
            func: Box::new(CExpr::Var("sym.imp.strlen".to_string())),
            args: vec![CExpr::Var("s".to_string())],
        });
        assert_eq!(
            normalized,
            CExpr::Var("len".to_string()),
            "expected owned strlen call expression to rewrite to len, got {normalized:?}; call_sources={:?}; aliases={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state.analysis_ctx.use_info.call_result_aliases
        );
    }

    #[test]
    fn x86_imported_malloc_arg_reuses_owned_strlen_inside_add() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x401140, "sym.imp.strlen".to_string()),
            (0x401190, "sym.imp.malloc".to_string()),
        ])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym.imp.strlen".to_string(),
                FunctionType {
                    return_type: CType::UInt(64),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: false,
                },
            ),
            (
                "sym.imp.malloc".to_string(),
                FunctionType {
                    return_type: CType::ptr(CType::Int(8)),
                    params: vec![CType::UInt(64)],
                    variadic: false,
                },
            ),
        ]));
        let mut s_home = stack_var_spec("s_home", Some(CType::ptr(CType::Int(8))), Some("rbp"));
        s_home.role = r2types::ExternalStackSlotRole::ParamHome;
        s_home.param_index = Some(0);
        s_home.param_name = Some("s".to_string());
        s_home.source_reg = Some("rdi".to_string());
        ctx.set_external_stack_vars(HashMap::from([
            (-0x18, s_home),
            (
                -0x8,
                stack_var_spec("len", Some(CType::UInt(64)), Some("rbp")),
            ),
        ]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([(
            "rdi".to_string(),
            "s".to_string(),
        )])));

        let rbp = make_var("rbp", 1, 8);
        let s_slot = make_var("tmp:s_slot", 1, 8);
        let s_load = make_var("tmp:11f80", 1, 8);
        let len_slot = make_var("tmp:len_slot", 1, 8);
        let len_store = make_var("tmp:6b00", 1, 8);
        let len_load = make_var("tmp:11f80", 2, 8);
        let len_tmp = make_var("rax", 3, 8);
        let malloc_arg = make_var("rax", 4, 8);

        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: s_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:ffffffffffffffe8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: s_slot.clone(),
                val: make_var("rdi", 0, 8),
            },
            SSAOp::Load {
                dst: s_load.clone(),
                space: "ram".to_string(),
                addr: s_slot.clone(),
            },
            SSAOp::Copy {
                dst: make_var("rax", 1, 8),
                src: s_load,
            },
            SSAOp::Copy {
                dst: make_var("rdi", 1, 8),
                src: make_var("rax", 1, 8),
            },
            SSAOp::Call {
                target: make_var("ram:401140", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 2, 8),
            },
            SSAOp::IntAdd {
                dst: len_slot.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Copy {
                dst: len_store.clone(),
                src: make_var("rax", 2, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: len_slot.clone(),
                val: len_store,
            },
            SSAOp::Load {
                dst: len_load.clone(),
                space: "ram".to_string(),
                addr: len_slot,
            },
            SSAOp::Copy {
                dst: len_tmp.clone(),
                src: len_load,
            },
            SSAOp::IntAdd {
                dst: malloc_arg.clone(),
                a: len_tmp,
                b: make_var("const:1", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("rdi", 3, 8),
                src: malloc_arg,
            },
            SSAOp::Call {
                target: make_var("ram:401190", 0, 8),
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let call_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Call { target } if target.display_name() == "ram:401190_0"))
            .expect("malloc call index");
        let rendered = ctx.render_call_args_for_callee(
            &CExpr::Var("sym.imp.malloc".to_string()),
            ctx.call_args_map()
                .get(&(block.addr, call_idx))
                .cloned()
                .expect("malloc call args"),
        );
        assert_eq!(
            rendered,
            vec![CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("len".to_string()),
                CExpr::IntLit(1),
            )],
            "expected imported malloc arg to reuse len + 1, got {rendered:?}; call_args={:?}; aliases={:?}",
            ctx.call_args_map().get(&(block.addr, call_idx)),
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias
        );
    }

    #[test]
    fn x86_final_dup_owner_survives_intervening_memcpy_call() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x401140, "sym.imp.strlen".to_string()),
            (0x401170, "sym.imp.memcpy".to_string()),
            (0x401190, "sym.imp.malloc".to_string()),
        ])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym.imp.strlen".to_string(),
                FunctionType {
                    return_type: CType::UInt(64),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: false,
                },
            ),
            (
                "sym.imp.malloc".to_string(),
                FunctionType {
                    return_type: CType::ptr(CType::Int(8)),
                    params: vec![CType::UInt(64)],
                    variadic: false,
                },
            ),
            (
                "sym.imp.memcpy".to_string(),
                FunctionType {
                    return_type: CType::ptr(CType::Unknown),
                    params: vec![
                        CType::ptr(CType::Unknown),
                        CType::ptr(CType::Int(8)),
                        CType::UInt(64),
                    ],
                    variadic: false,
                },
            ),
        ]));
        let mut s_home = stack_var_spec("s_home", Some(CType::ptr(CType::Int(8))), Some("rbp"));
        s_home.role = r2types::ExternalStackSlotRole::ParamHome;
        s_home.param_index = Some(0);
        s_home.param_name = Some("s".to_string());
        s_home.source_reg = Some("rdi".to_string());
        ctx.set_external_stack_vars(HashMap::from([
            (-0x18, s_home),
            (
                -0x8,
                stack_var_spec("len", Some(CType::UInt(64)), Some("rbp")),
            ),
            (
                -0x10,
                stack_var_spec("dup", Some(CType::ptr(CType::Int(8))), Some("rbp")),
            ),
        ]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([(
            "rdi".to_string(),
            "s".to_string(),
        )])));

        let rbp = make_var("rbp", 1, 8);
        let s_slot = make_var("tmp:s_slot", 1, 8);
        let len_slot = make_var("tmp:len_slot", 1, 8);
        let dup_slot = make_var("tmp:dup_slot", 1, 8);
        let s_load = make_var("tmp:11f80", 1, 8);
        let len_load = make_var("tmp:11f80", 2, 8);
        let dup_load = make_var("tmp:11f80", 3, 8);
        let final_dup_load = make_var("tmp:11f80", 4, 8);
        let malloc_arg = make_var("rax", 4, 8);
        let malloc_result = make_var("rax", 5, 8);
        let memcpy_result = make_var("rax", 8, 8);
        let final_ret = make_var("rax", 10, 8);

        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: s_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:ffffffffffffffe8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: s_slot.clone(),
                val: make_var("rdi", 0, 8),
            },
            SSAOp::Load {
                dst: s_load.clone(),
                space: "ram".to_string(),
                addr: s_slot.clone(),
            },
            SSAOp::Copy {
                dst: make_var("rdi", 1, 8),
                src: s_load.clone(),
            },
            SSAOp::Call {
                target: make_var("ram:401140", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 2, 8),
            },
            SSAOp::IntAdd {
                dst: len_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: len_slot.clone(),
                val: make_var("rax", 2, 8),
            },
            SSAOp::Load {
                dst: len_load.clone(),
                space: "ram".to_string(),
                addr: len_slot.clone(),
            },
            SSAOp::IntAdd {
                dst: malloc_arg.clone(),
                a: len_load.clone(),
                b: make_var("const:1", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("rdi", 3, 8),
                src: malloc_arg,
            },
            SSAOp::Call {
                target: make_var("ram:401190", 0, 8),
            },
            SSAOp::CallDefine {
                dst: malloc_result.clone(),
            },
            SSAOp::IntAdd {
                dst: dup_slot.clone(),
                a: rbp.clone(),
                b: make_var("const:fffffffffffffff0", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: dup_slot.clone(),
                val: malloc_result,
            },
            SSAOp::Load {
                dst: dup_load.clone(),
                space: "ram".to_string(),
                addr: dup_slot.clone(),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 5, 8),
                space: "ram".to_string(),
                addr: len_slot.clone(),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:len_plus_one", 1, 8),
                a: make_var("tmp:11f80", 5, 8),
                b: make_var("const:1", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("rdx", 3, 8),
                src: make_var("tmp:len_plus_one", 1, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 6, 8),
                space: "ram".to_string(),
                addr: s_slot.clone(),
            },
            SSAOp::Copy {
                dst: make_var("rcx", 3, 8),
                src: make_var("tmp:11f80", 6, 8),
            },
            SSAOp::Copy {
                dst: make_var("rsi", 3, 8),
                src: make_var("rcx", 3, 8),
            },
            SSAOp::Copy {
                dst: make_var("rdi", 5, 8),
                src: dup_load.clone(),
            },
            SSAOp::Call {
                target: make_var("ram:401170", 0, 8),
            },
            SSAOp::CallDefine { dst: memcpy_result },
            SSAOp::Load {
                dst: final_dup_load.clone(),
                space: "ram".to_string(),
                addr: dup_slot,
            },
            SSAOp::Copy {
                dst: final_ret.clone(),
                src: final_dup_load,
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        assert_eq!(
            ctx.get_expr(&final_ret),
            CExpr::Var("dup".to_string()),
            "expected final return owner to stay bound to dup across the intervening memcpy call, got {:?}; aliases={:?}; defs={:?}; semantic={:?}",
            ctx.get_expr(&final_ret),
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state
                .analysis_ctx
                .use_info
                .definitions
                .get(&final_ret.display_name()),
            ctx.state
                .analysis_ctx
                .use_info
                .semantic_values
                .get(&final_ret.display_name())
        );
    }

    #[test]
    fn x86_my_strdup_like_body_and_exit_blocks_fold_to_memcpy_and_return_dup() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    cond: Varnode::constant(1, 1),
                    target: Varnode::constant(0x1008, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: Varnode::constant(0x1008, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: Varnode::register(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:s_slot", 1, 8),
                a: make_var("rbp", 1, 8),
                b: make_var("const:ffffffffffffffe8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:s_slot", 1, 8),
                val: make_var("rdi", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 1, 8),
                space: "ram".to_string(),
                addr: make_var("tmp:s_slot", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("rdi", 1, 8),
                src: make_var("tmp:11f80", 1, 8),
            },
            SSAOp::Call {
                target: make_var("ram:401140", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 2, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:len_slot", 1, 8),
                a: make_var("rbp", 1, 8),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:len_slot", 1, 8),
                val: make_var("rax", 2, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 2, 8),
                space: "ram".to_string(),
                addr: make_var("tmp:len_slot", 1, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("rax", 4, 8),
                a: make_var("tmp:11f80", 2, 8),
                b: make_var("const:1", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("rdi", 3, 8),
                src: make_var("rax", 4, 8),
            },
            SSAOp::Call {
                target: make_var("ram:401190", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 5, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:dup_slot", 1, 8),
                a: make_var("rbp", 1, 8),
                b: make_var("const:fffffffffffffff0", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:dup_slot", 1, 8),
                val: make_var("rax", 5, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 3, 8),
                space: "ram".to_string(),
                addr: make_var("tmp:dup_slot", 1, 8),
            },
            SSAOp::IntSub {
                dst: make_var("tmp:3eb80", 1, 8),
                a: make_var("tmp:11f80", 3, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntEqual {
                dst: make_var("zf", 3, 1),
                a: make_var("tmp:3eb80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::CBranch {
                target: make_var("ram:1008", 0, 8),
                cond: make_var("zf", 3, 1),
            },
        ];
        func.get_block_mut(0x1004).expect("body").ops = vec![
            SSAOp::Load {
                dst: make_var("tmp:11f80", 4, 8),
                space: "ram".to_string(),
                addr: make_var("tmp:len_slot", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("rax", 6, 8),
                src: make_var("tmp:11f80", 4, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 8, 8),
                a: make_var("rax", 6, 8),
                b: make_var("const:1", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("rdx", 3, 8),
                src: make_var("tmp:4700", 8, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 5, 8),
                space: "ram".to_string(),
                addr: make_var("tmp:s_slot", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("rcx", 3, 8),
                src: make_var("tmp:11f80", 5, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 6, 8),
                space: "ram".to_string(),
                addr: make_var("tmp:dup_slot", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("rax", 7, 8),
                src: make_var("tmp:11f80", 6, 8),
            },
            SSAOp::Copy {
                dst: make_var("rsi", 3, 8),
                src: make_var("rcx", 3, 8),
            },
            SSAOp::Copy {
                dst: make_var("rdi", 5, 8),
                src: make_var("rax", 7, 8),
            },
            SSAOp::Call {
                target: make_var("ram:401170", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 8, 8),
            },
            SSAOp::Branch {
                target: make_var("ram:1008", 0, 8),
            },
        ];
        func.get_block_mut(0x1008).expect("exit").ops = vec![
            SSAOp::Load {
                dst: make_var("tmp:11f80", 8, 8),
                space: "ram".to_string(),
                addr: make_var("tmp:dup_slot", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("rax", 10, 8),
                src: make_var("tmp:11f80", 8, 8),
            },
            SSAOp::Return {
                target: make_var("rip", 1, 8),
            },
        ];

        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x401140, "sym.imp.strlen".to_string()),
            (0x401170, "sym.imp.memcpy".to_string()),
            (0x401190, "sym.imp.malloc".to_string()),
        ])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym.imp.strlen".to_string(),
                FunctionType {
                    return_type: CType::UInt(64),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: false,
                },
            ),
            (
                "sym.imp.malloc".to_string(),
                FunctionType {
                    return_type: CType::ptr(CType::Int(8)),
                    params: vec![CType::UInt(64)],
                    variadic: false,
                },
            ),
            (
                "sym.imp.memcpy".to_string(),
                FunctionType {
                    return_type: CType::ptr(CType::Unknown),
                    params: vec![
                        CType::ptr(CType::Unknown),
                        CType::ptr(CType::Int(8)),
                        CType::UInt(64),
                    ],
                    variadic: false,
                },
            ),
        ]));
        let mut s_home = stack_var_spec("s_home", Some(CType::ptr(CType::Int(8))), Some("rbp"));
        s_home.role = r2types::ExternalStackSlotRole::ParamHome;
        s_home.param_index = Some(0);
        s_home.param_name = Some("s".to_string());
        s_home.source_reg = Some("rdi".to_string());
        ctx.set_external_stack_vars(HashMap::from([
            (-0x18, s_home),
            (
                -0x8,
                stack_var_spec("len", Some(CType::UInt(64)), Some("rbp")),
            ),
            (
                -0x10,
                stack_var_spec("dup", Some(CType::ptr(CType::Int(8))), Some("rbp")),
            ),
        ]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([(
            "rdi".to_string(),
            "s".to_string(),
        )])));

        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        ctx.analyze_blocks(&fold_blocks);
        ctx.analyze_function_structure(&func);

        assert!(
            ctx.state
                .analysis_ctx
                .ownership
                .has_visible_owner_name("dup"),
            "expected semantic ownership facts to keep dup as a visible owned call result, got {:?}",
            ctx.state.analysis_ctx.ownership
        );
        let malloc_source = ctx
            .state
            .analysis_ctx
            .ownership
            .source_for_alias("tmp:11f80_8")
            .expect("malloc result source");
        let malloc_fact = ctx
            .state
            .analysis_ctx
            .ownership
            .ownership_for_source(malloc_source)
            .expect("malloc ownership fact");
        assert!(
            malloc_fact
                .owner
                .as_ref()
                .is_some_and(|owner| owner.visible_name == "dup"),
            "expected malloc ownership to resolve to dup, got {malloc_fact:?}"
        );

        let cond_expr = ctx
            .extract_condition_from_block(func.get_block(0x1000).expect("entry"))
            .expect("entry condition");
        assert!(
            matches!(
                &cond_expr,
                CExpr::Binary {
                    op: BinaryOp::Eq,
                    left,
                    right,
                } if matches!(left.as_ref(), CExpr::Var(name) if name == "dup")
                    && matches!(right.as_ref(), CExpr::IntLit(0))
            ) || matches!(
                &cond_expr,
                CExpr::Unary {
                    op: UnaryOp::Not,
                    operand,
                } if matches!(operand.as_ref(), CExpr::Var(name) if name == "dup")
            ),
            "expected my_strdup null-check to reuse the owned dup alias, got {cond_expr:?}"
        );
        assert!(
            !expr_contains_var(&cond_expr, "tmp:11f80"),
            "my_strdup null-check should not leak the stack reload temp, got {cond_expr:?}"
        );

        let body_block = func.get_block(0x1004).expect("body");
        let call_idx = body_block
            .ops
            .iter()
            .position(
                |op| matches!(op, SSAOp::Call { target } if target.display_name() == "ram:401170_0"),
            )
            .expect("memcpy call index");
        let rendered_args = ctx.render_call_args_for_callee(
            &CExpr::Var("sym.imp.memcpy".to_string()),
            ctx.call_args_map()
                .get(&(body_block.addr, call_idx))
                .cloned()
                .expect("memcpy call args"),
        );
        assert_eq!(
            rendered_args,
            vec![
                CExpr::Var("dup".to_string()),
                CExpr::Var("s".to_string()),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("len".to_string()),
                    CExpr::IntLit(1),
                ),
            ],
            "expected direct imported memcpy args to reuse dup, s, and len + 1, got {rendered_args:?}; call_args={:?}; stable_stack_values={:?}; tmp4700={:?}; rdx3={:?}",
            ctx.call_args_map().get(&(body_block.addr, call_idx)),
            ctx.state.analysis_ctx.use_info.stable_stack_values,
            ctx.state
                .analysis_ctx
                .use_info
                .semantic_values
                .get("tmp:4700_8"),
            ctx.state.analysis_ctx.use_info.semantic_values.get("RDX_3"),
        );

        let body_stmts = ctx.fold_block(func.get_block(0x1004).expect("body"), 0x1004);
        assert!(
            body_stmts.iter().any(|stmt| {
                matches!(
                    stmt,
                    CStmt::Expr(CExpr::Call { func, args })
                        if **func == CExpr::Var("sym.imp.memcpy".to_string())
                            && args
                                == &vec![
                                    CExpr::Var("dup".to_string()),
                                    CExpr::Var("s".to_string()),
                                    CExpr::binary(
                                        BinaryOp::Add,
                                        CExpr::Var("len".to_string()),
                                        CExpr::IntLit(1),
                                    ),
                                ]
                )
            }),
            "expected body block to fold to memcpy(dup, s, len + 1), got {body_stmts:?}"
        );

        let exit_stmts = ctx.fold_block(func.get_block(0x1008).expect("exit"), 0x1008);
        let Some(CStmt::Return(Some(exit_expr))) = exit_stmts.last() else {
            panic!("exit block should fold to return dup, got {exit_stmts:?}");
        };
        assert_eq!(exit_expr, &CExpr::Var("dup".to_string()));
    }

    #[test]
    fn dead_ephemeral_compare_temp_rewrites_to_owned_call_result_assignment() {
        let mut ctx = FoldingContext::new(64);
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401000,
            "sym.imp.atoi".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.atoi".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: false,
            },
        )]));
        ctx.state
            .analysis_ctx
            .flag_info
            .flag_only_values
            .insert("t3ea00".to_string());

        let source_call = (0x1000, 4);
        let source_id = CallSiteId::from(source_call);
        let call_expr = CExpr::call(
            CExpr::Var("sym.imp.atoi".to_string()),
            vec![CExpr::Subscript {
                base: Box::new(CExpr::Var("argv".to_string())),
                index: Box::new(CExpr::IntLit(1)),
            }],
        );
        ctx.state
            .analysis_ctx
            .ownership
            .call_expr_sources
            .entry(call_expr_cache_key(&call_expr))
            .or_default()
            .insert(source_id);
        ctx.state.analysis_ctx.ownership.call_ownership.insert(
            source_id,
            CallOwnershipFact {
                source: source_id,
                owner: Some(CallOwner {
                    visible_name: "var_4h".to_string(),
                    kind: CallOwnerKind::StableStackLocal,
                }),
                aliases: BTreeSet::new(),
                direct_aliases: BTreeSet::new(),
                call_expr_keys: BTreeSet::new(),
            },
        );

        let expr = CExpr::assign(
            CExpr::Var("t3ea00".to_string()),
            CExpr::binary(BinaryOp::Sub, call_expr.clone(), CExpr::IntLit(43)),
        );
        let normalized = ctx.normalize_final_assign_expr(expr);
        assert_eq!(
            normalized,
            CExpr::assign(CExpr::Var("var_4h".to_string()), call_expr),
            "expected dead compare temp to recover the owned call-result assignment"
        );
    }

    #[test]
    fn x86_fallthrough_return_arm_before_pure_epilogue_keeps_return_context() {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        use r2ssa::SSAFunction;

        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1008, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut false_arm = R2ILBlock::new(0x1004, 4);
        false_arm.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });
        let mut true_arm = R2ILBlock::new(0x1008, 4);
        true_arm.push(R2ILOp::Nop);
        let mut exit = R2ILBlock::new(0x100c, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        let mut func = SSAFunction::from_blocks_raw_no_arch(&[entry, false_arm, true_arm, exit])
            .expect("ssa func");
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::Copy {
                dst: make_var("rdi", 1, 8),
                src: make_var("const:6", 0, 8),
            },
            SSAOp::Call {
                target: make_var("ram:401120", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 2, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 1, 8),
                a: make_var("rbp", 1, 8),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 1, 8),
                val: make_var("rax", 2, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 1, 8),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:3ea80", 1, 8),
                src: make_var("tmp:11f80", 1, 8),
            },
            SSAOp::IntSub {
                dst: make_var("tmp:3eb80", 1, 8),
                a: make_var("tmp:3ea80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntEqual {
                dst: make_var("zf", 2, 1),
                a: make_var("tmp:3eb80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:12800", 1, 1),
                src: make_var("zf", 2, 1),
            },
            SSAOp::CBranch {
                target: make_var("ram:1008", 0, 8),
                cond: make_var("tmp:12800", 1, 1),
            },
        ];
        func.get_block_mut(0x1004).expect("false arm").ops = vec![
            SSAOp::Copy {
                dst: make_var("rax", 3, 8),
                src: make_var("const:0", 0, 8),
            },
            SSAOp::Branch {
                target: make_var("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x1008).expect("true arm").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 2, 8),
                a: make_var("rbp", 1, 8),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 2, 8),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 2, 8),
            },
            SSAOp::Copy {
                dst: make_var("rax", 4, 8),
                src: make_var("tmp:11f80", 2, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11e00", 1, 1),
                space: "ram".to_string(),
                addr: make_var("rax", 4, 8),
            },
            SSAOp::IntZExt {
                dst: make_var("eax", 2, 4),
                src: make_var("tmp:11e00", 1, 1),
            },
            SSAOp::IntZExt {
                dst: make_var("rax", 5, 8),
                src: make_var("eax", 2, 4),
            },
        ];
        func.get_block_mut(0x100c).expect("exit").ops = vec![SSAOp::Return {
            target: make_var("rip", 1, 8),
        }];

        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401120,
            "sym.imp.setlocale".to_string(),
        )])));
        ctx.inputs.type_hints = Box::leak(Box::new(HashMap::from([
            ("loc".to_string(), CType::ptr(CType::Int(8))),
            ("local_8".to_string(), CType::ptr(CType::Int(8))),
            ("rax_4".to_string(), CType::ptr(CType::Int(8))),
            ("RAX_4".to_string(), CType::ptr(CType::Int(8))),
        ])));
        ctx.inputs.function_return_type = Some(Box::leak(Box::new(CType::Int(32))));
        ctx.set_external_stack_vars(HashMap::from([(
            -0x8,
            stack_var_spec("loc", Some(CType::ptr(CType::Int(8))), Some("rbp")),
        )]));

        ctx.analyze_blocks(&func.blocks().cloned().collect::<Vec<_>>());
        ctx.analyze_function_structure(&func);

        assert!(
            ctx.state.return_blocks.contains(&0x1004),
            "false arm should be a return context, got {:?}",
            ctx.state.return_blocks
        );
        assert!(
            ctx.state.return_blocks.contains(&0x1008),
            "fallthrough true arm should be a return context, got {:?}",
            ctx.state.return_blocks
        );

        let byte_var = make_var("tmp:11e00", 1, 1);
        let byte_expr = ctx.get_expr(&byte_var);
        let byte_expr_is_temporary = matches!(
            byte_expr,
            CExpr::Var(ref name)
                if r2ssa::SSAVarNameKind::classify(&name.to_ascii_lowercase()).is_temporary()
        );
        assert!(
            !byte_expr_is_temporary,
            "byte load in the true arm should not regress to a transient temp before return tracking, got {byte_expr:?}",
        );

        let false_stmts = ctx.fold_block(func.get_block(0x1004).expect("false"), 0x1004);
        let Some(CStmt::Return(Some(false_expr))) = false_stmts.last() else {
            panic!("false arm should fold to return 0, got {false_stmts:?}");
        };
        assert_eq!(false_expr, &CExpr::IntLit(0));

        let true_stmts = ctx.fold_block(func.get_block(0x1008).expect("true"), 0x1008);
        let Some(CStmt::Return(Some(true_expr))) = true_stmts.last() else {
            panic!("true arm should fold to return loc[0], got {true_stmts:?}");
        };
        assert!(
            matches!(true_expr, CExpr::Subscript { .. })
                || matches!(true_expr, CExpr::Deref(_))
                || matches!(true_expr, CExpr::Cast { expr, .. } if matches!(expr.as_ref(), CExpr::Var(name) if name == "loc"))
                || matches!(true_expr, CExpr::Cast { expr, .. } if matches!(expr.as_ref(), CExpr::Var(_)))
                || matches!(true_expr, CExpr::Cast { expr, .. } if matches!(expr.as_ref(), CExpr::Subscript { .. } | CExpr::Deref(_))),
            "expected true arm to keep the loaded byte return shape, got {true_expr:?}"
        );
    }

    #[test]
    fn x86_local_branch_condition_for_direct_call_result_prefers_named_owner_alias() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401120,
            "sym.imp.setlocale".to_string(),
        )])));

        let owner = make_var("tmp:loc", 1, 8);
        let cmp_tmp = make_var("tmp:3ea80", 1, 8);
        let cmp_sub = make_var("tmp:3eb80", 1, 8);
        let zf = make_var("zf", 3, 1);
        let cond = make_var("tmp:12800", 1, 1);

        let block = make_block(vec![
            SSAOp::Copy {
                dst: make_var("rdi", 1, 8),
                src: make_var("const:6", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("rsi", 1, 8),
                src: make_var("const:0", 0, 8),
            },
            SSAOp::Call {
                target: make_var("ram:401120", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 1, 8),
            },
            SSAOp::Copy {
                dst: owner.clone(),
                src: make_var("rax", 1, 8),
            },
            SSAOp::Copy {
                dst: cmp_tmp.clone(),
                src: owner.clone(),
            },
            SSAOp::IntSub {
                dst: cmp_sub.clone(),
                a: cmp_tmp,
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntEqual {
                dst: zf.clone(),
                a: cmp_sub,
                b: make_var("const:0", 0, 8),
            },
            SSAOp::BoolNot {
                dst: cond.clone(),
                src: zf,
            },
            SSAOp::CBranch {
                target: make_var("ram:401158", 0, 8),
                cond: cond.clone(),
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let rhs = ctx.resolve_predicate_rhs_for_var(&cond, ctx.get_expr(&cond));
        assert!(
            rhs == CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("loc".to_string()),
                CExpr::IntLit(0)
            ) || matches!(
                rhs,
                CExpr::Binary {
                    op: BinaryOp::Ne,
                    ref left,
                    ref right,
                } if matches!(left.as_ref(), CExpr::Call { .. })
                    && matches!(right.as_ref(), CExpr::IntLit(0))
            ),
            "expected local branch condition to keep a stable call-result predicate shape, got {rhs:?}"
        );
    }

    #[test]
    fn x86_local_branch_condition_for_no_calldefine_imported_result_uses_call_expr() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401130,
            "sym.imp.strcmp".to_string(),
        )])));
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x403014,
            "secret123".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.strcmp".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8)), CType::ptr(CType::Int(8))],
                variadic: false,
            },
        )]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([(
            "rdi".to_string(),
            "password".to_string(),
        )])));

        let block = make_block(vec![
            SSAOp::Copy {
                dst: make_var("rsi", 1, 8),
                src: make_var("const:403014", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("rdi", 1, 8),
                src: make_var("rdi", 0, 8),
            },
            SSAOp::Call {
                target: make_var("ram:401130", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("cf", 2, 1),
                src: make_var("const:0", 0, 1),
            },
            SSAOp::Copy {
                dst: make_var("of", 2, 1),
                src: make_var("const:0", 0, 1),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:70400", 1, 4),
                a: make_var("EAX", 0, 4),
                b: make_var("EAX", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("ZF", 2, 1),
                a: make_var("tmp:70400", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:12800", 1, 1),
                src: make_var("ZF", 2, 1),
            },
            SSAOp::CBranch {
                cond: make_var("tmp:12800", 1, 1),
                target: make_var("const:401140", 0, 8),
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let cond_expr = ctx
            .extract_condition_from_block(&block)
            .expect("local branch condition");
        assert!(
            matches!(
                cond_expr,
                CExpr::Binary {
                    op: BinaryOp::Ne,
                    ref left,
                    ref right,
                } if matches!(
                    left.as_ref(),
                    CExpr::Call { func, args }
                        if **func == CExpr::Var("sym.imp.strcmp".to_string())
                            && args
                                == &vec![
                                    CExpr::Var("password".to_string()),
                                    CExpr::StringLit("secret123".to_string()),
                                ]
                ) && matches!(right.as_ref(), CExpr::IntLit(0))
            ),
            "expected no-calldefine imported-result branch condition to use the call expression, got {cond_expr:?}; call_sources={:?}; defs={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state.analysis_ctx.use_info.definitions
        );
    }

    #[test]
    fn x86_local_branch_condition_for_calldefine_imported_result_uses_call_expr() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401130,
            "sym.imp.strcmp".to_string(),
        )])));
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x403014,
            "secret123".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.strcmp".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8)), CType::ptr(CType::Int(8))],
                variadic: false,
            },
        )]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([(
            "rdi".to_string(),
            "password".to_string(),
        )])));

        let block = make_block(vec![
            SSAOp::Copy {
                dst: make_var("rsi", 1, 8),
                src: make_var("const:403014", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("rdi", 1, 8),
                src: make_var("rdi", 0, 8),
            },
            SSAOp::Call {
                target: make_var("ram:401130", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 2, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rdi", 2, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rsi", 2, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rdx", 2, 8),
            },
            SSAOp::Copy {
                dst: make_var("cf", 2, 1),
                src: make_var("const:0", 0, 1),
            },
            SSAOp::Copy {
                dst: make_var("of", 2, 1),
                src: make_var("const:0", 0, 1),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:70400", 1, 4),
                a: make_var("rax", 2, 8),
                b: make_var("rax", 2, 8),
            },
            SSAOp::IntEqual {
                dst: make_var("zf", 2, 1),
                a: make_var("tmp:70400", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:12800", 1, 1),
                src: make_var("zf", 2, 1),
            },
            SSAOp::CBranch {
                cond: make_var("tmp:12800", 1, 1),
                target: make_var("const:401140", 0, 8),
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let cond_expr = ctx
            .extract_condition_from_block(&block)
            .expect("local branch condition");
        assert!(
            matches!(
                cond_expr,
                CExpr::Binary {
                    op: BinaryOp::Ne,
                    ref left,
                    ref right,
                } if matches!(
                    left.as_ref(),
                    CExpr::Call { func, args }
                        if **func == CExpr::Var("sym.imp.strcmp".to_string())
                            && args
                                == &vec![
                                    CExpr::Var("password".to_string()),
                                    CExpr::StringLit("secret123".to_string()),
                                ]
                ) && matches!(right.as_ref(), CExpr::IntLit(0))
            ),
            "expected calldefine imported-result branch condition to use the call expression, got {cond_expr:?}; call_sources={:?}; defs={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state.analysis_ctx.use_info.definitions
        );
    }

    #[test]
    fn test_imported_call_arg_var_uses_semantic_alias_to_resolve_string_literal() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401030, "sym.imp.printf".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.printf".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            },
        );
        ctx.set_known_function_signatures(sigs);
        let mut strings = HashMap::new();
        strings.insert(0x40229e, "Unknown test: %d\\n".to_string());
        ctx.inputs.strings = Box::leak(Box::new(strings));
        ctx.state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert("tmp:fmt_1".to_string(), "t19".to_string());
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            "tmp:fmt_1".to_string(),
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Expr(CExpr::binary(
                BinaryOp::Add,
                CExpr::UIntLit(0x402000),
                CExpr::IntLit(0x29e),
            ))),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((0x1000, 0), vec![call_arg(CExpr::Var("t19".to_string()))]);

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401030", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], CExpr::StringLit("Unknown test: %d\\n".to_string()));
    }

    #[test]
    fn test_imported_call_arg_rendered_alias_uses_ssa_definition_chain_for_string_literal() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401030, "sym.imp.printf".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.printf".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            },
        );
        ctx.set_known_function_signatures(sigs);
        let mut strings = HashMap::new();
        strings.insert(0x100002292, "usage: vuln_test <n>\\n".to_string());
        ctx.inputs.strings = Box::leak(Box::new(strings));
        ctx.state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert("X0_13".to_string(), "t17".to_string());
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("t17".to_string(), CExpr::IntLit(658));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "X0_13".to_string(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("X0_4".to_string()),
                CExpr::IntLit(658),
            ),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("X0_4".to_string(), CExpr::UIntLit(0x100002000));
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((0x1000, 0), vec![call_arg(CExpr::Var("t17".to_string()))]);

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401030", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert_eq!(
            args[0],
            CExpr::StringLit("usage: vuln_test <n>\\n".to_string())
        );
    }

    #[test]
    fn test_imported_call_arg_phi_root_prefers_string_literal_source() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401030, "sym.imp.printf".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.printf".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            },
        );
        ctx.set_known_function_signatures(sigs);
        let mut strings = HashMap::new();
        strings.insert(0x100002638, "Unknown test: %d\\n".to_string());
        ctx.inputs.strings = Box::leak(Box::new(strings));
        ctx.state.analysis_ctx.use_info.phi_sources.insert(
            "X0_1".to_string(),
            vec![
                make_var("const:100002638", 0, 8),
                make_var("stack_178", 0, 8),
            ],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((0x1000, 0), vec![call_arg(CExpr::Var("X0_1".to_string()))]);

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401030", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], CExpr::StringLit("Unknown test: %d\\n".to_string()));
    }

    #[test]
    fn test_imported_call_arg_phi_root_prefers_semantic_pointer_source_over_stack_placeholder() {
        let mut ctx = FoldingContext::new(64);
        let mut names = HashMap::new();
        names.insert(0x401040, "sym.imp.atoi".to_string());
        ctx.set_function_names(names);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.atoi".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: false,
            },
        );
        ctx.set_known_function_signatures(sigs);
        ctx.state.analysis_ctx.use_info.phi_sources.insert(
            "X0_1".to_string(),
            vec![make_var("arg2", 0, 8), make_var("stack_178", 0, 8)],
        );
        ctx.state
            .analysis_ctx
            .stack_info
            .stack_vars
            .insert(0x178, "arg2".to_string());
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((0x1000, 0), vec![call_arg(CExpr::Var("X0_1".to_string()))]);

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401040", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert!(
            expr_contains_var(&args[0], "arg2"),
            "expected semantic pointer root to win, got: {:?}",
            args[0]
        );
        assert!(
            !expr_contains_var(&args[0], "stack_178") && !expr_contains_var(&args[0], "X0_1"),
            "phi-root imported arg should not keep placeholder or merged SSA var, got: {:?}",
            args[0]
        );
    }

    #[test]
    fn certified_phi_source_resolution_refuses_divergent_sources() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch).with_name("phi_refusal");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.state.analysis_ctx.use_info.phi_sources.insert(
            "RAX_3".to_string(),
            vec![
                make_var("const:1", 0, 8),
                make_var("const:2", 0, 8),
            ],
        );

        let mut visited = HashSet::new();
        let resolved = ctx.resolve_expr_from_phi_sources("RAX_3", 0, &mut visited, false);
        assert_eq!(
            resolved, None,
            "certified non-identity phi cannot pick one source as a fake expression"
        );
    }

    #[test]
    fn test_constant_pointer_offset_load_renders_as_subscript() {
        let mut ctx = FoldingContext::new(64);
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([(
            "x1".to_string(),
            "argv".to_string(),
        )])));
        ctx.set_type_hints(HashMap::from([(
            "argv".to_string(),
            CType::ptr(CType::ptr(CType::Int(8))),
        )]));

        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("argv".to_string()),
            CExpr::IntLit(8),
        );
        let rendered = ctx
            .debug_render_memory_access_from_visible_expr(&expr, 8)
            .expect("pointer offset load should render");

        match rendered {
            CExpr::Subscript { base, index } => {
                assert_eq!(*base, CExpr::Var("argv".to_string()));
                assert_eq!(*index, CExpr::IntLit(1));
            }
            other => panic!("expected constant-index subscript, got: {other:?}"),
        }
    }

    #[test]
    fn test_integer_linear_addition_collects_nested_terms_deterministically() {
        let mut ctx = FoldingContext::new(64);
        ctx.set_type_hints(HashMap::from([
            ("a".to_string(), CType::Int(32)),
            ("b".to_string(), CType::Int(32)),
        ]));

        let expr = ctx.identity_simplify_binary(
            BinaryOp::Add,
            CExpr::Var("b".to_string()),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("a".to_string()),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("a".to_string()),
                    CExpr::Var("a".to_string()),
                ),
            ),
            Some(4),
        );

        assert_eq!(
            expr,
            CExpr::binary(
                BinaryOp::Add,
                CExpr::binary(BinaryOp::Mul, CExpr::Var("a".to_string()), CExpr::IntLit(3)),
                CExpr::Var("b".to_string())
            )
        );
    }

    #[test]
    fn test_linear_addition_refuses_pointer_terms() {
        let mut ctx = FoldingContext::new(64);
        ctx.set_type_hints(HashMap::from([
            ("buf".to_string(), CType::ptr(CType::UInt(8))),
            ("i".to_string(), CType::Int(32)),
        ]));

        let expr = ctx.identity_simplify_binary(
            BinaryOp::Add,
            CExpr::Var("buf".to_string()),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("i".to_string()),
                CExpr::Var("i".to_string()),
            ),
            Some(8),
        );

        assert_eq!(
            expr,
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("buf".to_string()),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("i".to_string()),
                    CExpr::Var("i".to_string())
                )
            ),
            "pointer arithmetic must not be reordered or collapsed by scalar linear normalization"
        );
    }

    #[test]
    fn test_registry_arity_resolution_handles_prefixed_and_ssa_suffixed_names() {
        let ctx = FoldingContext::new(64);
        assert_eq!(
            ctx.non_variadic_call_arity(&CExpr::Var("sym.imp.strcmp".to_string())),
            Some(2)
        );
        assert_eq!(
            ctx.non_variadic_call_arity(&CExpr::Var("sym.imp.strcmp_0".to_string())),
            Some(2)
        );
    }

    #[test]
    fn test_registry_arity_can_cap_broken_known_signature_arity() {
        let mut ctx = FoldingContext::new(64);
        let mut sigs = HashMap::new();
        sigs.insert(
            "sym.imp.strcmp".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::void_ptr(), CType::void_ptr(), CType::void_ptr()],
                variadic: false,
            },
        );
        ctx.set_known_function_signatures(sigs);

        assert_eq!(
            ctx.non_variadic_call_arity(&CExpr::Var("sym.imp.strcmp".to_string())),
            Some(2),
            "embedded registry should cap malformed known signature arity for common libc calls"
        );
    }

    #[test]
    fn typed_callee_identity_signature_controls_direct_address_arity_and_return_type() {
        let mut ctx = make_x86_64_ctx();
        ctx.set_function_names(HashMap::from([(
            0x401050,
            "sym.imp.memcpy@plt".to_string(),
        )]));
        ctx.set_known_function_signatures(HashMap::from([(
            "memcpy".to_string(),
            FunctionType {
                return_type: CType::ptr(CType::Void),
                params: vec![CType::void_ptr(), CType::void_ptr(), CType::UInt(64)],
                variadic: false,
            },
        )]));

        let callee = CExpr::Var("const:401050".to_string());
        assert_eq!(ctx.non_variadic_call_arity(&callee), Some(3));
        assert!(
            ctx.known_signature_for_callee_expr(&callee).is_some(),
            "direct address aliases should attach the r2types-owned known signature"
        );
        assert_eq!(
            ctx.expr_type_hint(&CExpr::call(callee, vec![])),
            Some(CType::ptr(CType::Void))
        );
    }

    #[test]
    fn known_signature_does_not_make_internal_call_imported() {
        let mut ctx = make_x86_64_ctx();
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.helper".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::Int(32)],
                variadic: false,
            },
        )]));

        let callee = CExpr::Var("sym.helper".to_string());
        assert_eq!(ctx.non_variadic_call_arity(&callee), Some(1));
        assert!(
            ctx.known_signature_for_callee_expr(&callee).is_some(),
            "known signature remains available as type/arity evidence"
        );
        assert!(
            !ctx.is_imported_call_target(&callee),
            "type evidence must not be reclassified as import evidence"
        );
    }

    #[test]
    fn typed_callee_identity_signature_controls_void_call_detection() {
        let mut ctx = make_x86_64_ctx();
        ctx.set_function_names(HashMap::from([
            (0x401080, "sym.imp.free".to_string()),
            (0x401090, "sym.helper".to_string()),
        ]));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "free".to_string(),
                FunctionType {
                    return_type: CType::Void,
                    params: vec![CType::void_ptr()],
                    variadic: false,
                },
            ),
            (
                "sym.helper".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: Vec::new(),
                    variadic: false,
                },
            ),
        ]));

        assert!(ctx.call_expr_returns_void(&CExpr::call(
            CExpr::Var("const:401080".to_string()),
            vec![CExpr::Var("ptr".to_string())],
        )));
        assert!(!ctx.call_expr_returns_void(&CExpr::call(
            CExpr::Var("const:401090".to_string()),
            vec![],
        )));
    }

    #[test]
    fn expr_type_hint_preserves_cast_and_paren_contracts() {
        let mut ctx = make_x86_64_ctx();
        ctx.set_type_hints(HashMap::from([("value".to_string(), CType::UInt(64))]));

        assert_eq!(
            ctx.expr_type_hint(&CExpr::cast(
                CType::Int(16),
                CExpr::Var("value".to_string())
            )),
            Some(CType::Int(16))
        );
        assert_eq!(
            ctx.expr_type_hint(&CExpr::Paren(Box::new(CExpr::Var("value".to_string())))),
            Some(CType::UInt(64))
        );
    }

    #[test]
    fn test_is_cpu_flag() {
        assert!(is_cpu_flag("cf"));
        assert!(is_cpu_flag("zf"));
        assert!(is_cpu_flag("sf"));
        assert!(is_cpu_flag("cf_1"));
        assert!(is_cpu_flag("ng"));
        assert!(is_cpu_flag("zr"));
        assert!(is_cpu_flag("tmpng"));
        assert!(is_cpu_flag("tmpzr_1"));
        assert!(!is_cpu_flag("rax"));
        assert!(!is_cpu_flag("rbp"));
    }

    #[test]
    fn test_arm64_registers_are_treated_as_register_like_artifacts() {
        let ctx = FoldingContext::new(64);
        assert!(ctx.inputs.arch.is_register_like_base_name("x8"));
        assert!(ctx.inputs.arch.is_register_like_base_name("w9"));
        assert!(ctx.inputs.arch.is_register_like_base_name("x30"));
    }

    #[test]
    fn generated_carrier_name_uses_colon_rule_for_raw_storage_names() {
        assert!(is_generated_carrier_name("tmp:raw_1"));
        assert!(is_generated_carrier_name("unique:raw_1"));
        assert!(is_generated_carrier_name("space1:20"));
        assert!(is_generated_carrier_name("value_3"));
        assert!(is_generated_carrier_name("t19"));
        assert!(!is_generated_carrier_name("tmp_loop"));
        assert!(!is_generated_carrier_name("rax_1"));
    }

    #[test]
    fn switch_selector_simplification_uses_typed_static_table_base_names() {
        let ctx = FoldingContext::new(64);
        for base in ["sym.jump_table", "obj.jump_table", "0x401000"] {
            let expr = CExpr::Subscript {
                base: Box::new(CExpr::Var(base.to_string())),
                index: Box::new(CExpr::Var("selector".to_string())),
            };
            assert_eq!(
                ctx.simplify_switch_selector_expr(expr),
                CExpr::Var("selector".to_string()),
                "{base}",
            );
        }

        for base in [
            CExpr::UIntLit(0x401000),
            CExpr::IntLit(0x401000),
            CExpr::StringLit(".rodata.jump_table".to_string()),
        ] {
            let expr = CExpr::Subscript {
                base: Box::new(base),
                index: Box::new(CExpr::Var("selector".to_string())),
            };
            assert_eq!(
                ctx.simplify_switch_selector_expr(expr),
                CExpr::Var("selector".to_string()),
            );
        }

        for base in ["table", "tmp:1000_0", "arg1"] {
            let expr = CExpr::Subscript {
                base: Box::new(CExpr::Var(base.to_string())),
                index: Box::new(CExpr::Var("selector".to_string())),
            };
            assert_eq!(ctx.simplify_switch_selector_expr(expr.clone()), expr, "{base}");
        }

        let low_signal_index = CExpr::Subscript {
            base: Box::new(CExpr::Var("sym.jump_table".to_string())),
            index: Box::new(CExpr::Var("tmp:idx_0".to_string())),
        };
        assert_eq!(
            ctx.simplify_switch_selector_expr(low_signal_index.clone()),
            low_signal_index
        );

        let non_old_global_kind = CExpr::Subscript {
            base: Box::new(CExpr::Var("data.jump_table".to_string())),
            index: Box::new(CExpr::Var("selector".to_string())),
        };
        assert_eq!(
            ctx.simplify_switch_selector_expr(non_old_global_kind.clone()),
            non_old_global_kind
        );

        let invalid_hex = CExpr::Subscript {
            base: Box::new(CExpr::Var("0xnot_hex".to_string())),
            index: Box::new(CExpr::Var("selector".to_string())),
        };
        assert_eq!(
            ctx.simplify_switch_selector_expr(invalid_hex.clone()),
            invalid_hex
        );
    }

    #[test]
    fn typed_ssa_var_storage_filters_exclude_const_and_memory_sources() {
        let ctx = FoldingContext::new(64);
        let block = make_block(vec![
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("ram:401000", 0, 8),
                val: make_var("const:1", 0, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("ptr", 1, 8),
                val: make_var("value", 1, 4),
            },
        ]);

        let names = ctx.emitted_var_names(&[block]);
        assert!(names.contains("ptr_1"), "{names:?}");
        assert!(names.contains("value_1"), "{names:?}");
        assert!(
            names.iter().all(|name| {
                !r2ssa::SSAVarNameKind::classify(&name.to_ascii_lowercase()).is_constant()
                    && !name.eq_ignore_ascii_case("ram:401000")
            }),
            "{names:?}"
        );
    }

    #[test]
    fn typed_ssa_var_storage_filters_dead_storage_classification() {
        let ctx = FoldingContext::new(64);

        assert!(ctx.is_dead(&make_var("tmp:dead", 1, 8)));
        assert!(ctx.is_dead(&make_var("const:1", 0, 8)));
        assert!(ctx.is_dead(&make_var("reg:10", 1, 8)));
        assert!(!ctx.is_dead(&make_var("ram:401000", 0, 8)));
        assert!(!ctx.is_dead(&make_var("sym.helper", 0, 8)));
        assert!(!ctx.is_dead(&make_var("ordinary", 1, 8)));
    }

    #[test]
    fn typed_ssa_var_storage_filters_resolve_memory_without_stealing_constant_path() {
        let mut ctx = FoldingContext::new(64);
        ctx.set_function_names(HashMap::from([(0x401000, "target".to_string())]));

        assert_eq!(
            ctx.get_expr(&make_var("ram:401000", 0, 8)),
            CExpr::Var("target".to_string())
        );
        assert_eq!(
            ctx.get_expr(&make_var("const:402000", 0, 8)),
            CExpr::IntLit(0x402000)
        );
    }

    #[test]
    fn typed_ssa_var_storage_filters_memory_copy_lowers_to_assignment() {
        let ctx = FoldingContext::new(64);
        let stmt = ctx
            .op_to_stmt(&SSAOp::Copy {
                dst: make_var("ram:401000", 1, 8),
                src: make_var("value", 2, 8),
            })
            .expect("memory-destination copy should emit an assignment");

        let CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) = stmt
        else {
            panic!("expected assignment expression");
        };
        assert!(
            matches!(left.as_ref(), CExpr::Var(name) if name == "ram:401000_1"),
            "{left:?}"
        );
        assert!(
            matches!(right.as_ref(), CExpr::Var(name) if name == "value_2"),
            "{right:?}"
        );
    }

    #[test]
    fn assignment_lhs_uses_typed_ssa_kind_for_versioned_arg_carriers() {
        fn lowered_lhs_for(dst: SSAVar) -> CExpr {
            let mut ctx = FoldingContext::new(64);
            ctx.state
                .analysis_ctx
                .use_info
                .var_aliases
                .insert(dst.display_name(), "arg1".to_string());

            let stmt = ctx
                .op_to_stmt(&SSAOp::Copy {
                    dst,
                    src: make_var("value", 2, 8),
                })
                .expect("versioned generic-arg carrier should lower to an assignment");

            let CStmt::Expr(CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                ..
            }) = stmt
            else {
                panic!("expected assignment expression");
            };
            *left
        }

        assert_eq!(lowered_lhs_for(make_var("reg:10", 2, 8)), CExpr::Var("r10_2".to_string()));
        assert_eq!(lowered_lhs_for(make_var("reg:zf", 2, 1)), CExpr::Var("zf_2".to_string()));
        assert_eq!(lowered_lhs_for(make_var("tmp:11f80", 2, 8)), CExpr::Var("t2".to_string()));
        assert_eq!(lowered_lhs_for(make_var("unique:11f80", 2, 8)), CExpr::Var("t2".to_string()));
        assert_eq!(
            lowered_lhs_for(make_var("TMP:11f80", 2, 8)),
            CExpr::Var("tmp_11f80_2".to_string())
        );
        assert_eq!(
            lowered_lhs_for(make_var("reg:10", 0, 8)),
            CExpr::Var("arg1".to_string())
        );
    }

    #[test]
    fn test_dead_flag_elimination() {
        let rax_0 = make_var("RAX", 0, 8);
        let rax_1 = make_var("RAX", 1, 8);
        let zf_1 = make_var("ZF", 1, 1);
        let const_1 = make_var("const:1", 0, 8);

        let block = make_block(vec![
            // RAX_1 = RAX_0 + 1 (used)
            SSAOp::IntAdd {
                dst: rax_1.clone(),
                a: rax_0.clone(),
                b: const_1.clone(),
            },
            // ZF_1 = RAX_1 == 0 (not used - should be eliminated)
            SSAOp::IntEqual {
                dst: zf_1.clone(),
                a: rax_1.clone(),
                b: make_var("const:0", 0, 8),
            },
            // Store RAX_1 (uses RAX_1)
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("const:0x1000", 0, 8),
                val: rax_1,
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);

        // ZF_1 should be dead (flag, not used)
        assert!(ctx.is_dead(&zf_1));
    }

    #[test]
    fn test_single_use_inlining() {
        let rax_0 = make_var("RAX", 0, 8);
        let rbx_0 = make_var("RBX", 0, 8);
        let t0 = make_var("tmp:100", 0, 8);
        let t1 = make_var("tmp:100", 1, 8);

        let block = make_block(vec![
            // t0 = rax_0 + rbx_0 (single use)
            SSAOp::IntAdd {
                dst: t0.clone(),
                a: rax_0.clone(),
                b: rbx_0.clone(),
            },
            // t1 = t0 * 2
            SSAOp::IntMult {
                dst: t1.clone(),
                a: t0.clone(),
                b: make_var("const:2", 0, 8),
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);

        // t0 should be inlined (single use, temp)
        assert!(ctx.should_inline(&t0));
    }

    #[test]
    fn test_multi_use_simple_temp_inlining() {
        let rax_0 = make_var("RAX", 0, 8);
        let t0 = make_var("tmp:200", 1, 8);
        let t1 = make_var("tmp:201", 1, 8);
        let t2 = make_var("tmp:202", 1, 8);

        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: t0.clone(),
                a: rax_0,
                b: make_var("const:1", 0, 8),
            },
            SSAOp::IntAdd {
                dst: t1.clone(),
                a: t0.clone(),
                b: t0.clone(),
            },
            SSAOp::IntAdd {
                dst: t2,
                a: t1,
                b: t0.clone(),
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);

        // t0 has 3 uses but remains simple enough to inline.
        assert!(ctx.should_inline(&t0));
    }

    #[test]
    fn should_inline_ssavar_guard_matrix_preserves_refusal_order() {
        fn mark_use(ctx: &mut FoldingContext<'_>, var: &SSAVar, count: usize) {
            ctx.state
                .analysis_ctx
                .use_info
                .use_counts
                .insert(var.display_name(), count);
        }

        fn mark_simple_def(ctx: &mut FoldingContext<'_>, var: &SSAVar) {
            ctx.state
                .analysis_ctx
                .use_info
                .definitions
                .insert(var.display_name(), CExpr::IntLit(1));
        }

        let mut ctx = FoldingContext::new(64);

        let zero_use = make_var("tmp:zero", 1, 8);
        assert!(!ctx.should_inline(&zero_use));

        let too_many_simple = make_var("ordinary_many", 1, 8);
        mark_use(&mut ctx, &too_many_simple, 4);
        mark_simple_def(&mut ctx, &too_many_simple);
        assert!(!ctx.should_inline(&too_many_simple));

        let three_use_simple = make_var("ordinary_three", 1, 8);
        mark_use(&mut ctx, &three_use_simple, 3);
        mark_simple_def(&mut ctx, &three_use_simple);
        assert!(ctx.should_inline(&three_use_simple));

        let pinned = make_var("pinned_value", 1, 8);
        mark_use(&mut ctx, &pinned, 1);
        ctx.state
            .analysis_ctx
            .use_info
            .pinned
            .insert(pinned.display_name());
        assert!(!ctx.should_inline(&pinned));

        let direct_unowned = make_var("tmp:123", 1, 8);
        mark_use(&mut ctx, &direct_unowned, 1);
        ctx.state
            .analysis_ctx
            .use_info
            .direct_call_result_aliases
            .insert(direct_unowned.display_name());
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert(direct_unowned.display_name(), (0x1000, 1));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .entry((0x1000, 1))
            .or_default()
            .insert(direct_unowned.display_name());
        assert!(ctx.should_inline(&direct_unowned));

        let direct_owned = make_var("tmp:owned", 1, 8);
        mark_use(&mut ctx, &direct_owned, 1);
        ctx.state
            .analysis_ctx
            .use_info
            .direct_call_result_aliases
            .insert(direct_owned.display_name());
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert(direct_owned.display_name(), (0x1000, 2));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .entry((0x1000, 2))
            .or_default()
            .insert(direct_owned.display_name());
        assert!(!ctx.should_inline(&direct_owned));

        let condition_non_candidate = make_var("condition_value", 1, 8);
        mark_use(&mut ctx, &condition_non_candidate, 1);
        ctx.state
            .analysis_ctx
            .use_info
            .condition_vars
            .insert(condition_non_candidate.display_name());
        assert!(!ctx.should_inline(&condition_non_candidate));

        let condition_flag = make_var("ZF", 1, 1);
        mark_use(&mut ctx, &condition_flag, 1);
        ctx.state
            .analysis_ctx
            .use_info
            .condition_vars
            .insert(condition_flag.display_name());
        assert!(ctx.should_inline(&condition_flag));

        let flag_only = make_var("flag_only", 1, 8);
        mark_use(&mut ctx, &flag_only, 2);
        ctx.state
            .analysis_ctx
            .flag_info
            .flag_only_values
            .insert(flag_only.display_name());
        assert!(ctx.should_inline(&flag_only));

        let multi_complex_caller_saved = make_var("RDI", 1, 8);
        mark_use(&mut ctx, &multi_complex_caller_saved, 2);
        assert!(!ctx.should_inline(&multi_complex_caller_saved));

        let single_ordinary = make_var("ordinary_single", 1, 8);
        mark_use(&mut ctx, &single_ordinary, 1);
        assert!(ctx.should_inline(&single_ordinary));

        let stack_base = make_var("RSP", 1, 8);
        mark_use(&mut ctx, &stack_base, 1);
        assert!(!ctx.should_inline(&stack_base));

        let return_reg = make_var("RAX", 1, 8);
        mark_use(&mut ctx, &return_reg, 1);
        assert!(ctx.should_inline(&return_reg));
        ctx.state.return_blocks.insert(0x2000);
        ctx.current_block_addr.set(Some(0x2000));
        assert!(!ctx.should_inline(&return_reg));
        ctx.current_block_addr.set(None);
    }

    #[test]
    fn test_fold_block() {
        let rax_0 = make_var("RAX", 0, 8);
        let rax_1 = make_var("RAX", 1, 8);
        let zf_1 = make_var("ZF", 1, 1);
        let const_1 = make_var("const:1", 0, 8);

        let block = make_block(vec![
            // RAX_1 = RAX_0 + 1
            SSAOp::IntAdd {
                dst: rax_1.clone(),
                a: rax_0.clone(),
                b: const_1.clone(),
            },
            // ZF_1 = RAX_1 == 0 (unused flag)
            SSAOp::IntEqual {
                dst: zf_1.clone(),
                a: rax_1.clone(),
                b: make_var("const:0", 0, 8),
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);
        let stmts = ctx.fold_block(&block, block.addr);

        // RAX_1 is used only once (in the dead ZF_1 expression), so with stronger
        // inlining it gets inlined into the dead expression, which is then eliminated.
        // Both statements should be eliminated.
        assert_eq!(stmts.len(), 0);
    }

    #[test]
    fn test_member_access_uses_oracle_field_name() {
        let base = make_var("arg1", 0, 8);
        let addr = make_var("tmp:9100", 1, 8);
        let dst = make_var("tmp:9101", 1, 4);
        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: addr.clone(),
                a: base.clone(),
                b: make_var("const:0x30", 0, 8),
            },
            SSAOp::Load {
                dst: dst.clone(),
                space: "ram".to_string(),
                addr: addr.clone(),
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        let mut hints = HashMap::new();
        hints.insert(base.display_name(), CType::ptr(CType::Int(32)));
        ctx.set_type_hints(hints);
        let oracle = make_oracle_for_member(base, 0x30, "thirteenth");
        ctx.set_type_oracle(Some(&oracle));
        ctx.analyze_block(&block);

        let expr = ctx.op_to_expr(&SSAOp::Load {
            dst,
            space: "ram".to_string(),
            addr,
        });
        let CExpr::PtrMember { member, .. } = expr else {
            panic!("expected pointer member access");
        };
        assert_eq!(member, "thirteenth");
    }

    #[test]
    fn test_member_access_falls_back_without_oracle_name() {
        let base = make_var("arg1", 0, 8);
        let addr = make_var("tmp:9200", 1, 8);
        let dst = make_var("tmp:9201", 1, 4);
        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: addr.clone(),
                a: base.clone(),
                b: make_var("const:0x30", 0, 8),
            },
            SSAOp::Load {
                dst: dst.clone(),
                space: "ram".to_string(),
                addr: addr.clone(),
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        let mut hints = HashMap::new();
        hints.insert(base.display_name(), CType::ptr(CType::Int(32)));
        ctx.set_type_hints(hints);
        ctx.analyze_block(&block);

        let expr = ctx.op_to_expr(&SSAOp::Load {
            dst,
            space: "ram".to_string(),
            addr,
        });
        assert!(
            !matches!(expr, CExpr::PtrMember { .. } | CExpr::Member { .. }),
            "member syntax should not be invented without oracle-backed field names"
        );
    }

    #[test]
    fn test_get_return_expr_semanticizes_raw_member_derefs_from_typed_base() {
        let base = make_var("arg1", 0, 8);
        let ret = make_var("tmp:9300", 1, 8);
        let mut ctx = FoldingContext::new(64);
        ctx.set_type_hints(
            [(
                base.display_name(),
                CType::ptr(CType::Struct("DemoStruct".to_string())),
            )]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demostruct".to_string(),
                ExternalStruct {
                    name: "DemoStruct".to_string(),
                    fields: [
                        (
                            0,
                            ExternalField {
                                name: "first".to_string(),
                                offset: 0,
                                ty: Some("int32_t".to_string()),
                            },
                        ),
                        (
                            0x30,
                            ExternalField {
                                name: "thirteenth".to_string(),
                                offset: 0x30,
                                ty: Some("int32_t".to_string()),
                            },
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            ret.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Deref(Box::new(CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var(base.display_name()),
                    CExpr::IntLit(0x30),
                ))),
                CExpr::Deref(Box::new(CExpr::Var(base.display_name()))),
            ),
        );

        let expr = ctx.get_return_expr(&ret);
        let CExpr::Binary { left, right, .. } = expr else {
            panic!("expected semanticized binary return");
        };
        assert!(
            matches!(left.as_ref(), CExpr::PtrMember { member, .. } if member == "thirteenth"),
            "expected left side to resolve to thirteenth field, got {left:?}"
        );
        assert!(
            matches!(right.as_ref(), CExpr::PtrMember { member, .. } if member == "first"),
            "expected right side to resolve to first field, got {right:?}"
        );
    }

    #[test]
    fn test_get_return_expr_semanticizes_raw_member_derefs_from_visible_arg_alias() {
        let ret = make_var("tmp:9301", 1, 8);
        let mut ctx = FoldingContext::new(64);
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [("rdi".to_string(), "arg1".to_string())]
                .into_iter()
                .collect(),
        ));
        ctx.set_type_hints(
            [(
                "arg1".to_string(),
                CType::ptr(CType::Struct("DemoStruct".to_string())),
            )]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demostruct".to_string(),
                ExternalStruct {
                    name: "DemoStruct".to_string(),
                    fields: [
                        (
                            0,
                            ExternalField {
                                name: "first".to_string(),
                                offset: 0,
                                ty: Some("int32_t".to_string()),
                            },
                        ),
                        (
                            0x30,
                            ExternalField {
                                name: "thirteenth".to_string(),
                                offset: 0x30,
                                ty: Some("int32_t".to_string()),
                            },
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            ret.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Deref(Box::new(CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("arg1".to_string()),
                    CExpr::IntLit(0x30),
                ))),
                CExpr::Deref(Box::new(CExpr::Var("arg1".to_string()))),
            ),
        );

        let expr = ctx.get_return_expr(&ret);
        let CExpr::Binary { left, right, .. } = expr else {
            panic!("expected semanticized binary return");
        };
        assert!(
            matches!(left.as_ref(), CExpr::PtrMember { member, .. } if member == "thirteenth"),
            "expected left side to resolve visible arg alias back to the SSA-backed field, got {left:?}"
        );
        assert!(
            matches!(right.as_ref(), CExpr::PtrMember { member, .. } if member == "first"),
            "expected right side to resolve visible arg alias back to the SSA-backed field, got {right:?}"
        );
    }

    #[test]
    fn test_subscript_rejects_pointer_typed_local_as_index_and_uses_scalar_index() {
        let arr = make_var("arg1", 0, 8);
        let addr = make_var("tmp:9300", 1, 8);
        let load = make_var("tmp:9301", 1, 4);
        let bogus_index = make_var("tmp:9302", 1, 8);
        let real_index = make_var("tmp:9303", 1, 4);

        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.use_info.ptr_arith.insert(
            addr.display_name(),
            PtrArith {
                base: arr.clone(),
                index: bogus_index.clone(),
                element_size: 4,
                is_sub: false,
            },
        );
        ctx.state.analysis_ctx.use_info.definitions.insert(
            bogus_index.display_name(),
            CExpr::Var("local_8".to_string()),
        );
        ctx.state.analysis_ctx.use_info.definitions.insert(
            addr.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("arg1".to_string()),
                CExpr::binary(
                    BinaryOp::Mul,
                    CExpr::Var("local_c".to_string()),
                    CExpr::IntLit(4),
                ),
            ),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .type_hints
            .insert("local_8".to_string(), CType::ptr(CType::Int(32)));
        ctx.state
            .analysis_ctx
            .use_info
            .type_hints
            .insert("local_c".to_string(), CType::Int(32));
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert(real_index.display_name(), CExpr::Var("local_c".to_string()));
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            real_index.display_name(),
            crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Expr(CExpr::Var(
                "local_c".to_string(),
            ))),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            load.display_name(),
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(
                        arr.clone(),
                    )),
                    index: Some(crate::analysis::ValueRef::from(real_index.clone())),
                    scale_bytes: 4,
                    offset_bytes: 0,
                },
                size: 4,
            },
        );

        let mut visited = HashSet::new();
        let expr = ctx
            .render_semantic_value(
                ctx.state
                    .analysis_ctx
                    .use_info
                    .semantic_values
                    .get(&load.display_name())
                    .expect("semantic load should exist"),
                0,
                &mut visited,
            )
            .expect("semantic load should render");
        let CExpr::Subscript { ref index, .. } = expr else {
            panic!("expected subscript expression, got {expr:?}");
        };
        assert!(
            matches!(index.as_ref(), CExpr::Var(name) if name == "local_c"),
            "typed pointer locals must not survive as subscript indices, got {expr:?}"
        );
    }

    #[test]
    fn test_subscript_swaps_scalar_stack_slot_base_with_address_like_index() {
        let len_value = make_var("tmp:9400", 1, 8);
        let buf_value = make_var("tmp:9401", 1, 8);
        let store_addr = make_var("tmp:9402", 1, 8);

        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.use_info.stack_slots.insert(
            "len".to_string(),
            StackSlotProvenance {
                offset: -0x20,
                predicate_carrier: false,
                return_carrier: false,
                value_kind: StackSlotValueKind::Scalar,
            },
        );
        ctx.state.analysis_ctx.use_info.stack_slots.insert(
            "buf".to_string(),
            StackSlotProvenance {
                offset: -0x8,
                predicate_carrier: false,
                return_carrier: false,
                value_kind: StackSlotValueKind::AddressLike,
            },
        );
        ctx.state
            .analysis_ctx
            .use_info
            .type_hints
            .insert("len".to_string(), CType::u64());
        ctx.state
            .analysis_ctx
            .use_info
            .type_hints
            .insert("buf".to_string(), CType::ptr(CType::i8()));
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            len_value.display_name(),
            crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Expr(CExpr::Var(
                "len".to_string(),
            ))),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            buf_value.display_name(),
            crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Expr(CExpr::Var(
                "buf".to_string(),
            ))),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            store_addr.display_name(),
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(
                        len_value.clone(),
                    )),
                    index: Some(crate::analysis::ValueRef::from(buf_value.clone())),
                    scale_bytes: 1,
                    offset_bytes: 0,
                },
                size: 1,
            },
        );

        let mut visited = HashSet::new();
        let expr = ctx
            .render_semantic_value(
                ctx.state
                    .analysis_ctx
                    .use_info
                    .semantic_values
                    .get(&store_addr.display_name())
                    .expect("semantic load should exist"),
                0,
                &mut visited,
            )
            .expect("semantic load should render");
        let CExpr::Subscript { base, index } = expr else {
            panic!("expected subscript expression, got {expr:?}");
        };
        assert!(
            matches!(base.as_ref(), CExpr::Var(name) if name == "buf"),
            "address-like stack slot must be the subscript base, got base={base:?} index={index:?}"
        );
        assert!(
            matches!(index.as_ref(), CExpr::Var(name) if name == "len"),
            "scalar stack slot must remain the subscript index, got base={base:?} index={index:?}"
        );
    }

    #[test]
    fn semantic_index_storage_filter_uses_typed_ssa_name_kind_without_lowering() {
        let ctx = FoldingContext::new(64);

        assert!(!ctx.is_semantic_index_expr(&CExpr::Var("const:4_0".to_string())));
        assert!(!ctx.is_semantic_index_expr(&CExpr::Var("ram:401000_0".to_string())));
        assert!(ctx.is_semantic_index_expr(&CExpr::Var("CONST:4_0".to_string())));
        assert!(ctx.is_semantic_index_expr(&CExpr::Var("idx_1".to_string())));
        assert!(!ctx.is_semantic_index_expr(&CExpr::Var("stack".to_string())));
        assert!(!ctx.is_semantic_index_expr(&CExpr::Var("saved_fp".to_string())));
        assert!(!ctx.is_semantic_index_expr(&CExpr::Var("stack_8".to_string())));
    }

    #[test]
    fn low_signal_visible_name_uses_typed_storage_kind_and_display_heuristics() {
        let ctx = FoldingContext::new(64);

        assert!(ctx.is_low_signal_visible_name("tmp:1_0"));
        assert!(ctx.is_low_signal_visible_name("CONST:1_0"));
        assert!(ctx.is_low_signal_visible_name("RAM:401000_0"));
        assert!(ctx.is_low_signal_visible_name("tmp_loop_counter"));
        assert!(ctx.is_low_signal_visible_name("t19"));
        assert!(ctx.is_low_signal_visible_name("v3e_2"));
        assert!(!ctx.is_low_signal_visible_name("space1:20"));
        assert!(!ctx.is_low_signal_visible_name("value"));
        assert!(!ctx.is_low_signal_visible_name("rax_1"));
    }

    #[test]
    fn test_member_access_uses_subscript_base_when_base_has_generic_ptr_arith_definition() {
        let idx = make_var("arg2", 0, 4);
        let base = make_var("tmp:9400", 1, 8);
        let addr = make_var("tmp:9401", 1, 8);
        let dst = make_var("tmp:9402", 1, 4);
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .ptr_members
            .insert(addr.display_name(), (base.clone(), 8));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            base.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("arg1".to_string()),
                CExpr::binary(
                    BinaryOp::Mul,
                    CExpr::Var("arg2".to_string()),
                    CExpr::IntLit(56),
                ),
            ),
        );
        ctx.state.analysis_ctx.use_info.type_hints.insert(
            base.display_name(),
            CType::ptr(CType::Struct("DemoStruct".to_string())),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            dst.display_name(),
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(
                        make_var("arg1", 0, 8),
                    )),
                    index: Some(crate::analysis::ValueRef::from(idx.clone())),
                    scale_bytes: 56,
                    offset_bytes: 8,
                },
                size: 4,
            },
        );
        let oracle = make_oracle_for_member(base.clone(), 8, "third");
        ctx.set_type_oracle(Some(&oracle));

        let semantic = ctx
            .state
            .analysis_ctx
            .use_info
            .semantic_values
            .get(&dst.display_name())
            .expect("semantic member load should exist");
        let crate::analysis::SemanticValue::Load { addr, .. } = semantic else {
            panic!("expected semantic member load, got {semantic:?}");
        };
        assert_eq!(addr.offset_bytes, 8);
        assert!(
            addr.index.is_some() && addr.scale_bytes == 56,
            "generic ptr-arith base should stay as indexed semantic shape before rendering"
        );
        let _ = idx;
    }

    #[test]
    fn test_subscript_reconstructs_shift_scaled_index_expression() {
        let addr = make_var("tmp:9500", 1, 8);
        let dst = make_var("tmp:9501", 1, 4);
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .type_hints
            .insert("arg1".to_string(), CType::ptr(CType::Int(32)));
        ctx.state
            .analysis_ctx
            .use_info
            .type_hints
            .insert("arg2".to_string(), CType::Int(32));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            addr.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("arg1".to_string()),
                CExpr::binary(
                    BinaryOp::Shl,
                    CExpr::Var("arg2".to_string()),
                    CExpr::IntLit(2),
                ),
            ),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            dst.display_name(),
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(
                        make_var("arg1", 0, 8),
                    )),
                    index: Some(crate::analysis::ValueRef::from(make_var("arg2", 0, 4))),
                    scale_bytes: 4,
                    offset_bytes: 0,
                },
                size: 4,
            },
        );

        let mut visited = HashSet::new();
        let expr = ctx
            .render_semantic_value(
                ctx.state
                    .analysis_ctx
                    .use_info
                    .semantic_values
                    .get(&dst.display_name())
                    .expect("semantic load should exist"),
                0,
                &mut visited,
            )
            .expect("semantic load should render");
        let CExpr::Subscript { index, .. } = expr else {
            panic!("expected subscript expression, got {expr:?}");
        };
        assert!(
            matches!(index.as_ref(), CExpr::Var(name) if name == "arg2"),
            "shift-scaled index must preserve the semantic scalar index"
        );
    }

    #[test]
    fn test_typed_load_reconstructs_commuted_pointer_index_visible_address() {
        let addr = make_var("tmp:9550", 1, 8);
        let dst = make_var("tmp:9551", 1, 1);
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .type_hints
            .insert("buf".to_string(), CType::ptr(CType::u8()));
        ctx.state
            .analysis_ctx
            .use_info
            .type_hints
            .insert("i".to_string(), CType::u64());
        ctx.state.analysis_ctx.use_info.definitions.insert(
            addr.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("i".to_string()),
                CExpr::Var("buf".to_string()),
            ),
        );

        let direct = ctx
            .indexed_pointer_add_expr(
                &CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("i".to_string()),
                    CExpr::Var("buf".to_string()),
                ),
                &CType::u8(),
            )
            .expect("typed commuted pointer add should normalize directly");
        assert!(matches!(direct, CExpr::Subscript { .. }), "{direct:?}");

        let expr = ctx.render_canonical_load_expr(&dst, &addr, CType::u8());
        let CExpr::Subscript { base, index } = expr else {
            panic!("expected commuted pointer addition to render as subscript, got {expr:?}");
        };
        assert!(
            matches!(base.as_ref(), CExpr::Var(name) if name == "buf"),
            "typed pointer operand must be the subscript base, got base={base:?} index={index:?}"
        );
        assert!(
            matches!(index.as_ref(), CExpr::Var(name) if name == "i"),
            "scalar operand must be the subscript index, got base={base:?} index={index:?}"
        );
    }

    #[test]
    fn raw_ram_address_load_resolves_symbol_via_typed_memory_kind() {
        let addr = make_var("ram:404000", 0, 8);
        let dst = make_var("tmp:load", 1, 8);
        let mut ctx = FoldingContext::new(64);
        ctx.inputs.symbols = Box::leak(Box::new(HashMap::from([(
            0x404000,
            "obj.global_value".to_string(),
        )])));

        let expr = ctx.render_canonical_load_expr(&dst, &addr, CType::u64());

        assert_eq!(expr, CExpr::Var("obj.global_value".to_string()));
    }

    #[test]
    fn raw_ram_address_store_target_resolves_symbol_via_typed_memory_kind() {
        let addr = make_var("ram:404000", 0, 8);
        let mut ctx = FoldingContext::new(64);
        ctx.inputs.symbols = Box::leak(Box::new(HashMap::from([(
            0x404000,
            "obj.global_value".to_string(),
        )])));

        let expr = ctx.render_canonical_store_target_expr(&addr, 8, CType::u64());

        assert_eq!(expr, CExpr::Var("obj.global_value".to_string()));
    }

    #[test]
    fn test_member_access_reconstructs_combined_struct_array_index_scale() {
        let base = make_var("tmp:9600", 1, 8);
        let addr = make_var("tmp:9601", 1, 8);
        let dst = make_var("tmp:9602", 1, 4);
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .ptr_members
            .insert(addr.display_name(), (base.clone(), 8));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            base.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("arr".to_string()),
                CExpr::binary(
                    BinaryOp::Shl,
                    CExpr::binary(
                        BinaryOp::Sub,
                        CExpr::binary(
                            BinaryOp::Shl,
                            CExpr::Var("idx".to_string()),
                            CExpr::IntLit(3),
                        ),
                        CExpr::Var("idx".to_string()),
                    ),
                    CExpr::IntLit(3),
                ),
            ),
        );
        ctx.state.analysis_ctx.use_info.type_hints.insert(
            "arr".to_string(),
            CType::ptr(CType::Struct("DemoStruct".to_string())),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .type_hints
            .insert("idx".to_string(), CType::Int(32));
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            dst.display_name(),
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(
                        make_var("arr", 0, 8),
                    )),
                    index: Some(crate::analysis::ValueRef::from(make_var("idx", 0, 4))),
                    scale_bytes: 56,
                    offset_bytes: 8,
                },
                size: 4,
            },
        );
        let oracle = make_oracle_for_member(base.clone(), 8, "third");
        ctx.set_type_oracle(Some(&oracle));

        let semantic = ctx
            .state
            .analysis_ctx
            .use_info
            .semantic_values
            .get(&dst.display_name())
            .expect("semantic member load should exist");
        let crate::analysis::SemanticValue::Load { addr, .. } = semantic else {
            panic!("expected semantic member load, got {semantic:?}");
        };
        assert_eq!(addr.offset_bytes, 8);
        let Some(index) = &addr.index else {
            panic!("expected semantic indexed base, got {addr:?}");
        };
        assert!(
            index.var.name == "idx" && index.var.version == 0,
            "combined shift/sub scale should still recover the real struct-array index, got {index:?}"
        );
    }

    #[test]
    fn test_live_arm64_struct_array_store_keeps_semantic_base_after_stack_override_pass() {
        let sp0 = make_var("SP", 0, 8);
        let sp1 = make_var("SP", 1, 8);
        let x0 = make_var("X0", 0, 8);
        let w1 = make_var("W1", 0, 4);
        let w2 = make_var("W2", 0, 4);
        let tmp6500_1 = make_var("tmp:6500", 1, 8);
        let tmp6400_1 = make_var("tmp:6400", 1, 8);
        let tmp6500_2 = make_var("tmp:6500", 2, 8);
        let x9_1 = make_var("X9", 1, 8);
        let tmp6400_2 = make_var("tmp:6400", 2, 8);
        let tmp26b00_1 = make_var("tmp:26b00", 1, 4);
        let x10_1 = make_var("X10", 1, 8);
        let x10_2 = make_var("X10", 2, 8);
        let tmp12480_1 = make_var("tmp:12480", 1, 8);
        let x9_2 = make_var("X9", 2, 8);
        let tmp6400_3 = make_var("tmp:6400", 3, 8);

        let block = make_block(vec![
            SSAOp::IntSub {
                dst: sp1.clone(),
                a: sp0,
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntAdd {
                dst: tmp6500_1.clone(),
                a: sp1.clone(),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: tmp6500_1,
                val: x0.clone(),
            },
            SSAOp::IntAdd {
                dst: tmp6400_1.clone(),
                a: sp1.clone(),
                b: make_var("const:4", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: tmp6400_1,
                val: w1.clone(),
            },
            SSAOp::IntAdd {
                dst: tmp6500_2.clone(),
                a: sp1.clone(),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Load {
                dst: x9_1.clone(),
                space: "ram".to_string(),
                addr: tmp6500_2,
            },
            SSAOp::IntAdd {
                dst: tmp6400_2.clone(),
                a: sp1,
                b: make_var("const:4", 0, 8),
            },
            SSAOp::Load {
                dst: tmp26b00_1.clone(),
                space: "ram".to_string(),
                addr: tmp6400_2,
            },
            SSAOp::IntSExt {
                dst: x10_1.clone(),
                src: tmp26b00_1,
            },
            SSAOp::IntMult {
                dst: x10_2.clone(),
                a: x10_1,
                b: make_var("const:38", 0, 8),
            },
            SSAOp::IntAdd {
                dst: tmp12480_1.clone(),
                a: x9_1,
                b: x10_2,
            },
            SSAOp::Copy {
                dst: x9_2.clone(),
                src: tmp12480_1,
            },
            SSAOp::IntAdd {
                dst: tmp6400_3.clone(),
                a: x9_2,
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: tmp6400_3.clone(),
                val: w2,
            },
        ]);

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("x0".to_string(), "arg1".to_string()),
                ("x1".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                (
                    "arg1".to_string(),
                    CType::ptr(CType::Struct("DemoStruct".to_string())),
                ),
                ("arg2".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demostruct".to_string(),
                ExternalStruct {
                    name: "DemoStruct".to_string(),
                    fields: [
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
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));
        let oracle = make_oracle_for_members(x0.clone(), &[(8, "third"), (0x34, "fourteenth")]);
        ctx.set_type_oracle(Some(&oracle));
        ctx.analyze_block(&block);

        let semantic = ctx.lookup_semantic_value(&tmp6400_3.display_name());
        assert!(
            matches!(
                semantic,
                Some(crate::analysis::SemanticValue::Address(crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(value_ref),
                    index: Some(_),
                    scale_bytes: 56,
                    offset_bytes: 8,
                })) if value_ref.var == x0
            ) || matches!(
                semantic,
                Some(crate::analysis::SemanticValue::Address(crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Raw(CExpr::Var(name)),
                    index: Some(_),
                    scale_bytes: 56,
                    offset_bytes: 8,
                })) if name == "arg1"
            ),
            "actual semantic value: {semantic:?}"
        );

        let mut visited = HashSet::new();
        let rendered = ctx
            .render_memory_access_by_name(&tmp6400_3.display_name(), 4, 0, &mut visited)
            .expect("semantic store lhs should render");
        assert!(
            matches!(rendered, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "semantic store lhs should render as member access, got {rendered:?}"
        );
        let rendered_text = format!("{rendered:?}");
        assert!(
            rendered_text.contains("arg1") && !rendered_text.contains("stack_8"),
            "semantic member access should stay rooted at arg1, got {rendered:?}"
        );
    }

    #[test]
    fn test_indexed_member_render_uses_external_layout_hint_without_solver_type() {
        let base = make_var("X0", 0, 8);
        let index = make_var("W1", 0, 4);
        let addr = make_var("tmp:6400", 3, 8);

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("x0".to_string(), "arg1".to_string()),
                ("x1".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                (
                    "arg1".to_string(),
                    CType::ptr(CType::Typedef("DemoLayout".to_string())),
                ),
                ("arg2".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demolayout".to_string(),
                ExternalStruct {
                    name: "DemoLayout".to_string(),
                    fields: [
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
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            addr.display_name(),
            crate::analysis::SemanticValue::Address(crate::analysis::NormalizedAddr {
                base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(base)),
                index: Some(crate::analysis::ValueRef::from(index)),
                scale_bytes: 56,
                offset_bytes: 8,
            }),
        );

        let mut visited = HashSet::new();
        let rendered = ctx
            .render_memory_access_by_name(&addr.display_name(), 4, 0, &mut visited)
            .expect("indexed member with external layout hint should render");
        let rendered_text = format!("{rendered:?}");
        assert!(
            matches!(rendered, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected indexed-member render, got {rendered:?}"
        );
        assert!(
            rendered_text.contains("third") && rendered_text.contains("arg1"),
            "expected layout-backed field render rooted at arg1, got {rendered:?}"
        );
    }

    #[test]
    fn test_typedef_aggregate_without_layout_renders_observed_field_placeholders() {
        let base = make_var("X0", 0, 8);
        let addr = make_var("tmp:6400", 3, 8);

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [("x0".to_string(), "obj".to_string())]
                .into_iter()
                .collect(),
        ));
        ctx.set_type_hints(
            [(
                "obj".to_string(),
                CType::ptr(CType::Typedef("DemoStruct".to_string())),
            )]
            .into_iter()
            .collect(),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            addr.display_name(),
            crate::analysis::SemanticValue::Address(crate::analysis::NormalizedAddr {
                base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(base)),
                index: None,
                scale_bytes: 0,
                offset_bytes: 0x30,
            }),
        );

        let mut visited = HashSet::new();
        let rendered = ctx
            .render_memory_access_by_name(&addr.display_name(), 4, 0, &mut visited)
            .expect("typedef-backed aggregate access should render");

        assert_eq!(
            rendered,
            CExpr::PtrMember {
                base: Box::new(CExpr::Var("obj".to_string())),
                member: "f_30".to_string()
            }
        );
    }

    #[test]
    fn test_render_memory_access_from_visible_expr_recovers_indexed_member_from_raw_pointer_math() {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("x0".to_string(), "arg1".to_string()),
                ("x1".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                (
                    "arg1".to_string(),
                    CType::ptr(CType::Struct("demo_layout".to_string())),
                ),
                ("arg2".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demo_layout".to_string(),
                ExternalStruct {
                    name: "demo_layout".to_string(),
                    fields: [
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
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));

        let addr = CExpr::binary(
            BinaryOp::Add,
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("arg1".to_string()),
                CExpr::binary(
                    BinaryOp::Mul,
                    CExpr::Var("arg2".to_string()),
                    CExpr::IntLit(56),
                ),
            ),
            CExpr::IntLit(8),
        );

        let shape = ctx
            .normalized_addr_from_visible_expr(&addr, 0)
            .expect("raw pointer math should normalize to an indexed address");
        assert_eq!(shape.offset_bytes, 8);
        assert!(
            shape.index.is_some(),
            "expected recovered index, got {shape:?}"
        );

        let shape_depth_one = ctx
            .normalized_addr_from_visible_expr(&addr, 1)
            .expect("raw pointer math should normalize at nonzero recursion depth");
        assert_eq!(shape_depth_one.offset_bytes, 8);
        assert!(
            shape_depth_one.index.is_some(),
            "expected recovered index at depth one, got {shape_depth_one:?}"
        );

        let mut render_visited = HashSet::new();
        let direct = ctx
            .render_access_expr_from_addr(&shape, 4, 0, &mut render_visited)
            .expect("normalized indexed address should render");
        assert!(
            matches!(direct, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected direct indexed-member render, got {direct:?}"
        );

        let mut render_zero_visited = HashSet::new();
        let direct_zero = ctx
            .render_access_expr_from_addr(&shape, 0, 0, &mut render_zero_visited)
            .expect("normalized indexed address should render even without explicit elem_size");
        assert!(
            matches!(direct_zero, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected zero-sized direct indexed-member render, got {direct_zero:?}"
        );

        let mut direct_visible_visited = HashSet::new();
        let direct_visible = ctx
            .render_memory_access_from_visible_expr(&addr, 0, 0, &mut direct_visible_visited)
            .expect("raw visible pointer math should render through memory renderer");
        assert!(
            matches!(
                direct_visible,
                CExpr::Member { .. } | CExpr::PtrMember { .. }
            ),
            "expected visible raw pointer math to render as indexed-member, got {direct_visible:?}"
        );

        let mut visited = HashSet::new();
        let rendered = ctx.semanticize_visible_expr(&CExpr::Deref(Box::new(addr)), 0, &mut visited);
        let rendered_text = format!("{rendered:?}");
        assert!(
            matches!(rendered, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected indexed-member render, got {rendered:?}"
        );
        assert!(
            rendered_text.contains("third") && rendered_text.contains("arg1"),
            "expected layout-backed indexed member render, got {rendered:?}"
        );
    }

    #[test]
    fn test_semanticize_raw_subscript_recovers_exact_indexed_field_from_layout() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "items".to_string()),
                ("esi".to_string(), "idx".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                (
                    "items".to_string(),
                    CType::ptr(CType::Struct("Item".to_string())),
                ),
                ("idx".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "item".to_string(),
                ExternalStruct {
                    name: "Item".to_string(),
                    fields: [
                        (
                            0,
                            ExternalField {
                                name: "id".to_string(),
                                offset: 0,
                                ty: Some("int32_t".to_string()),
                            },
                        ),
                        (
                            4,
                            ExternalField {
                                name: "flags".to_string(),
                                offset: 4,
                                ty: Some("uint16_t".to_string()),
                            },
                        ),
                        (
                            6,
                            ExternalField {
                                name: "len".to_string(),
                                offset: 6,
                                ty: Some("uint16_t".to_string()),
                            },
                        ),
                        (
                            8,
                            ExternalField {
                                name: "scores".to_string(),
                                offset: 8,
                                ty: Some("int32_t[4]".to_string()),
                            },
                        ),
                        (
                            24,
                            ExternalField {
                                name: "next".to_string(),
                                offset: 24,
                                ty: Some("Item*".to_string()),
                            },
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));

        let raw = CExpr::Subscript {
            base: Box::new(CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("items".to_string()),
                CExpr::binary(
                    BinaryOp::Mul,
                    CExpr::Var("idx".to_string()),
                    CExpr::IntLit(40),
                ),
            )),
            index: Box::new(CExpr::IntLit(3)),
        };

        let semantic = ctx.debug_semanticize_visible_expr(&raw);
        let rendered = format!("{semantic:?}");
        assert!(
            matches!(semantic, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "raw subscript should promote only through exact layout proof, got {semantic:?}"
        );
        assert!(
            rendered.contains("len") && rendered.contains("items") && rendered.contains("idx"),
            "expected exact indexed len field, got {semantic:?}"
        );
        assert!(
            !rendered.contains("scores"),
            "field-width proof should not reinterpret the subscript as an array element, got {semantic:?}"
        );
    }

    #[test]
    fn test_render_memory_access_from_visible_expr_recovers_masked_x86_indexed_member() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arr".to_string()),
                ("esi".to_string(), "idx".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                (
                    "arr".to_string(),
                    CType::ptr(CType::Struct("demo_layout".to_string())),
                ),
                ("idx".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demo_layout".to_string(),
                ExternalStruct {
                    name: "demo_layout".to_string(),
                    fields: [
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
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));

        let shift_mask = CExpr::binary(BinaryOp::BitAnd, CExpr::IntLit(3), CExpr::IntLit(63));
        let scaled_index = CExpr::binary(
            BinaryOp::Shl,
            CExpr::binary(
                BinaryOp::Sub,
                CExpr::binary(
                    BinaryOp::Shl,
                    CExpr::Var("idx".to_string()),
                    shift_mask.clone(),
                ),
                CExpr::Var("idx".to_string()),
            ),
            shift_mask,
        );
        let addr = CExpr::binary(
            BinaryOp::Add,
            CExpr::binary(BinaryOp::Add, CExpr::Var("arr".to_string()), scaled_index),
            CExpr::IntLit(0x34),
        );

        let shape = ctx
            .normalized_addr_from_visible_expr(&addr, 0)
            .expect("masked x86 raw pointer math should normalize to an indexed address");
        assert_eq!(shape.offset_bytes, 0x34);
        assert!(
            shape.index.is_some() && shape.scale_bytes == 56,
            "expected masked x86 index recovery, got {shape:?}"
        );

        let rendered = ctx
            .debug_render_memory_access_from_visible_expr(&addr, 4)
            .expect("masked x86 raw pointer math should render as member access");
        let rendered_text = format!("{rendered:?}");
        assert!(
            matches!(rendered, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected indexed-member render, got {rendered:?}"
        );
        assert!(
            rendered_text.contains("fourteenth") && rendered_text.contains("arr"),
            "expected masked x86 member render rooted at arr, got {rendered:?}"
        );
    }

    #[test]
    fn test_normalized_addr_prefers_pointer_definition_over_scalar_stack_home_hint() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arr".to_string()),
                ("esi".to_string(), "idx".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                (
                    "arr".to_string(),
                    CType::ptr(CType::Struct("demo_layout".to_string())),
                ),
                ("idx".to_string(), CType::Int(32)),
                ("local_c".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demo_layout".to_string(),
                ExternalStruct {
                    name: "demo_layout".to_string(),
                    fields: [
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
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "local_c".to_string(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("arr".to_string()),
                CExpr::binary(
                    BinaryOp::Mul,
                    CExpr::Var("idx".to_string()),
                    CExpr::IntLit(56),
                ),
            ),
        );

        let addr = CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("local_c".to_string()),
            CExpr::IntLit(0x34),
        );
        let shape = ctx
            .normalized_addr_from_visible_expr(&addr, 0)
            .expect("scalar stack-home alias should still resolve through pointer definition");
        assert_eq!(shape.offset_bytes, 0x34);
        assert!(
            shape.index.is_some() && shape.scale_bytes == 56,
            "expected pointer definition to win over scalar local hint, got {shape:?}"
        );

        let rendered = ctx
            .debug_render_memory_access_from_visible_expr(&addr, 4)
            .expect("resolved pointer definition should render as member access");
        let rendered_text = format!("{rendered:?}");
        assert!(
            matches!(rendered, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected member render, got {rendered:?}"
        );
        assert!(
            rendered_text.contains("fourteenth") && rendered_text.contains("arr"),
            "expected resolved member render rooted at arr, got {rendered:?}"
        );
    }

    #[test]
    fn test_plain_indexed_load_does_not_upgrade_from_unrelated_field_name_any() {
        struct FieldNameAnyOnlyOracle;

        impl TypeOracle for FieldNameAnyOnlyOracle {
            fn type_of(&self, _var: &SSAVar) -> TypeId {
                0
            }

            fn struct_shape(&self, _ty: TypeId) -> Option<&StructShape> {
                None
            }

            fn is_pointer(&self, _ty: TypeId) -> bool {
                false
            }

            fn is_array(&self, _ty: TypeId) -> bool {
                false
            }

            fn field_name(&self, _ty: TypeId, _offset: u64) -> Option<&str> {
                None
            }

            fn field_name_any(&self, offset: u64) -> Option<&str> {
                (offset == 0).then_some("p0")
            }
        }

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("x0".to_string(), "arg1".to_string()),
                ("x1".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        let oracle = FieldNameAnyOnlyOracle;
        ctx.set_type_oracle(Some(&oracle));

        let addr = CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("arg1".to_string()),
            CExpr::binary(
                BinaryOp::Mul,
                CExpr::Var("arg2".to_string()),
                CExpr::IntLit(4),
            ),
        );

        let mut visited = HashSet::new();
        let rendered = ctx
            .render_memory_access_from_visible_expr(&addr, 4, 0, &mut visited)
            .expect("plain indexed pointer math should still render");

        assert!(
            matches!(rendered, CExpr::Subscript { .. }),
            "expected plain subscript, got {rendered:?}"
        );
        let rendered_text = format!("{rendered:?}");
        assert!(
            !rendered_text.contains("p0"),
            "field_name_any fallback must not manufacture placeholder member access, got {rendered:?}"
        );
    }

    #[test]
    fn test_load_generic_deref_inserts_minimal_pointer_cast() {
        let addr = make_var("tmp:9300", 1, 8);
        let dst = make_var("tmp:9301", 1, 4);
        let block = make_block(vec![SSAOp::Load {
            dst: dst.clone(),
            space: "ram".to_string(),
            addr: addr.clone(),
        }]);

        let mut ctx = FoldingContext::new(64);
        let mut hints = HashMap::new();
        hints.insert(addr.display_name(), CType::Int(64));
        hints.insert(dst.display_name(), CType::Int(32));
        ctx.set_type_hints(hints);
        ctx.analyze_block(&block);

        let stmt = ctx
            .op_to_stmt(&SSAOp::Load {
                dst,
                space: "ram".to_string(),
                addr,
            })
            .expect("load should emit statement");
        let CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            right,
            ..
        }) = stmt
        else {
            panic!("expected assignment expression");
        };
        let CExpr::Deref(inner) = right.as_ref() else {
            panic!("expected dereference expression");
        };
        assert!(
            matches!(
                inner.as_ref(),
                CExpr::Cast {
                    ty: CType::Pointer(_),
                    ..
                }
            ),
            "generic deref should cast integer-ish address to typed pointer"
        );
    }

    #[test]
    fn test_load_generic_deref_avoids_redundant_pointer_cast() {
        let addr = make_var("arg1", 0, 8);
        let dst = make_var("tmp:9401", 1, 4);
        let block = make_block(vec![SSAOp::Load {
            dst: dst.clone(),
            space: "ram".to_string(),
            addr: addr.clone(),
        }]);

        let mut ctx = FoldingContext::new(64);
        let mut hints = HashMap::new();
        hints.insert(addr.display_name(), CType::ptr(CType::Int(32)));
        hints.insert(dst.display_name(), CType::Int(32));
        ctx.set_type_hints(hints);
        ctx.analyze_block(&block);

        let stmt = ctx
            .op_to_stmt(&SSAOp::Load {
                dst,
                space: "ram".to_string(),
                addr,
            })
            .expect("load should emit statement");
        let CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            right,
            ..
        }) = stmt
        else {
            panic!("expected assignment expression");
        };
        let CExpr::Deref(inner) = right.as_ref() else {
            panic!("expected dereference expression");
        };
        assert!(
            !matches!(
                inner.as_ref(),
                CExpr::Cast {
                    ty: CType::Pointer(_),
                    ..
                }
            ),
            "address already typed as pointer should not get an extra cast"
        );
    }

    #[test]
    fn test_comparison_reconstruction() {
        // Test that CMP instruction pattern is reconstructed:
        // IntSub tmp = a - 0xdead
        // IntEqual ZF = tmp == 0
        // BoolNot cond = !ZF
        // CBranch cond  -> should become "if (a != 0xdead)"

        let edi_0 = make_var("EDI", 0, 4);
        let tmp_sub = make_var("tmp:1000", 1, 4);
        let zf_1 = make_var("ZF", 1, 1);
        let cond = make_var("tmp:2000", 1, 1);
        let const_dead = make_var("const:dead", 0, 4);
        let const_0 = make_var("const:0", 0, 4);

        let block = make_block(vec![
            // tmp_sub = edi_0 - 0xdead (the CMP)
            SSAOp::IntSub {
                dst: tmp_sub.clone(),
                a: edi_0.clone(),
                b: const_dead.clone(),
            },
            // ZF = tmp_sub == 0
            SSAOp::IntEqual {
                dst: zf_1.clone(),
                a: tmp_sub.clone(),
                b: const_0.clone(),
            },
            // cond = !ZF
            SSAOp::BoolNot {
                dst: cond.clone(),
                src: zf_1.clone(),
            },
            // CBranch cond
            SSAOp::CBranch {
                cond: cond.clone(),
                target: make_var("const:1000", 0, 8),
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);

        // Check that flag_origins was populated
        assert!(
            ctx.flag_origins_map().contains_key("ZF_1"),
            "ZF_1 should be in flag_origins"
        );

        // Check the origin values
        let (left, right) = ctx.flag_origins_map().get("ZF_1").unwrap();
        assert_eq!(left, "edi", "Left operand should be edi");
        assert_eq!(right, "0xdead", "Right operand should be 0xdead");
    }

    #[test]
    fn test_flag_only_transitive_marking() {
        let edi_0 = make_var("EDI", 0, 4);
        let tmp = make_var("tmp:3000", 1, 4);
        let zf_1 = make_var("ZF", 1, 1);
        let cond = make_var("tmp:3001", 1, 1);
        let const_0 = make_var("const:0", 0, 4);

        let block = make_block(vec![
            SSAOp::IntSub {
                dst: tmp.clone(),
                a: edi_0,
                b: const_0.clone(),
            },
            SSAOp::IntEqual {
                dst: zf_1.clone(),
                a: tmp.clone(),
                b: const_0,
            },
            SSAOp::BoolNot {
                dst: cond.clone(),
                src: zf_1,
            },
            SSAOp::CBranch {
                cond,
                target: make_var("const:1000", 0, 8),
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);

        assert!(ctx.flag_only_values_set().contains(&tmp.display_name()));
        assert!(ctx.is_dead(&tmp));
    }

    #[test]
    fn test_flag_only_preserved_for_non_flag_consumer() {
        let edi_0 = make_var("EDI", 0, 4);
        let tmp = make_var("tmp:4000", 1, 4);
        let zf_1 = make_var("ZF", 1, 1);
        let cond = make_var("tmp:4001", 1, 1);
        let const_0 = make_var("const:0", 0, 4);

        let block = make_block(vec![
            SSAOp::IntSub {
                dst: tmp.clone(),
                a: edi_0,
                b: const_0.clone(),
            },
            SSAOp::IntEqual {
                dst: zf_1.clone(),
                a: tmp.clone(),
                b: const_0.clone(),
            },
            SSAOp::BoolNot {
                dst: cond.clone(),
                src: zf_1,
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("const:0x2000", 0, 8),
                val: tmp.clone(),
            },
            SSAOp::CBranch {
                cond,
                target: make_var("const:1000", 0, 8),
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);

        assert!(!ctx.flag_only_values_set().contains(&tmp.display_name()));
        assert!(!ctx.is_dead(&tmp));
    }

    #[test]
    fn test_simplify_predicate_rewrites_cmp_zero() {
        let ctx = FoldingContext::new(64);
        let expr = CExpr::unary(
            UnaryOp::Not,
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::binary(BinaryOp::Sub, CExpr::Var("x".to_string()), CExpr::IntLit(0)),
                CExpr::IntLit(0),
            ),
        );
        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("x".to_string()), CExpr::IntLit(0))
        );
    }

    #[test]
    fn test_simplify_predicate_rewrites_sub_const_cmp_zero() {
        let ctx = FoldingContext::new(64);
        let expr = CExpr::binary(
            BinaryOp::Eq,
            CExpr::binary(
                BinaryOp::Sub,
                CExpr::Var("x".to_string()),
                CExpr::IntLit(0xdead),
            ),
            CExpr::IntLit(0),
        );
        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var("x".to_string()),
                CExpr::IntLit(0xdead)
            )
        );
    }

    #[test]
    fn test_simplify_predicate_rewrites_sub_var_cmp_zero() {
        let ctx = FoldingContext::new(64);
        let expr = CExpr::binary(
            BinaryOp::Ne,
            CExpr::binary(
                BinaryOp::Sub,
                CExpr::Var("x".to_string()),
                CExpr::Var("y".to_string()),
            ),
            CExpr::IntLit(0),
        );
        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("x".to_string()),
                CExpr::Var("y".to_string())
            )
        );
    }

    #[test]
    fn test_simplify_predicate_rewrites_sub_all_ones_cmp_zero() {
        let ctx = FoldingContext::new(64);
        let expr = CExpr::binary(
            BinaryOp::Eq,
            CExpr::binary(
                BinaryOp::Sub,
                CExpr::Var("x".to_string()),
                CExpr::UIntLit(0xffff_ffff),
            ),
            CExpr::IntLit(0),
        );
        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var("x".to_string()),
                CExpr::UIntLit(0xffff_ffff)
            )
        );
    }

    #[test]
    fn test_c_int_typedef_return_context_signs_32_bit_literals() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_return_type = Some(Box::leak(Box::new(CType::Typedef(
            "int".to_string(),
        ))));

        assert_eq!(
            ctx.get_return_expr(&make_var("const:ffffffff", 0, 4)),
            CExpr::IntLit(-1)
        );
        assert_eq!(
            ctx.get_return_expr(&make_var("const:fffffffe", 0, 4)),
            CExpr::IntLit(-2)
        );
    }

    #[test]
    fn test_simplify_predicate_rewrites_ne_ge_zero_to_gt_zero() {
        let ctx = FoldingContext::new(64);
        let expr = CExpr::binary(
            BinaryOp::And,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("x".to_string()), CExpr::IntLit(0)),
            CExpr::binary(BinaryOp::Ge, CExpr::Var("x".to_string()), CExpr::IntLit(0)),
        );
        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Gt, CExpr::Var("x".to_string()), CExpr::IntLit(0))
        );
    }

    #[test]
    fn test_simplify_predicate_rewrites_negated_casted_lt_or_eq_to_gt() {
        let ctx = FoldingContext::new(64);
        let expr = CExpr::unary(
            UnaryOp::Not,
            CExpr::binary(
                BinaryOp::Or,
                CExpr::binary(
                    BinaryOp::Lt,
                    CExpr::cast(CType::UInt(64), CExpr::Var("len".to_string())),
                    CExpr::cast(CType::UInt(64), CExpr::Var("64".to_string())),
                ),
                CExpr::binary(
                    BinaryOp::Eq,
                    CExpr::Var("len".to_string()),
                    CExpr::IntLit(100),
                ),
            ),
        );
        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Gt,
                CExpr::Var("len".to_string()),
                CExpr::IntLit(100)
            )
        );
    }

    #[test]
    fn test_identity_sub_zero() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::Sub,
            CExpr::Var("x".to_string()),
            CExpr::IntLit(0),
            Some(4),
        );
        assert_eq!(simplified, CExpr::Var("x".to_string()));
    }

    #[test]
    fn test_identity_add_zero() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::Add,
            CExpr::Var("x".to_string()),
            CExpr::IntLit(0),
            Some(4),
        );
        assert_eq!(simplified, CExpr::Var("x".to_string()));
    }

    #[test]
    fn test_identity_add_repeated_scaled_term() {
        let mut ctx = FoldingContext::new(64);
        ctx.set_type_hints(HashMap::from([("x".to_string(), CType::Int(32))]));
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::Add,
            CExpr::Var("x".to_string()),
            CExpr::binary(BinaryOp::Mul, CExpr::Var("x".to_string()), CExpr::IntLit(2)),
            Some(4),
        );
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Mul, CExpr::Var("x".to_string()), CExpr::IntLit(3))
        );
    }

    #[test]
    fn test_identity_or_zero() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::BitOr,
            CExpr::Var("x".to_string()),
            CExpr::IntLit(0),
            Some(4),
        );
        assert_eq!(simplified, CExpr::Var("x".to_string()));
    }

    #[test]
    fn test_identity_xor_zero() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::BitXor,
            CExpr::Var("x".to_string()),
            CExpr::IntLit(0),
            Some(4),
        );
        assert_eq!(simplified, CExpr::Var("x".to_string()));
    }

    #[test]
    fn test_identity_xor_self() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::BitXor,
            CExpr::Var("x".to_string()),
            CExpr::Var("x".to_string()),
            Some(4),
        );
        assert_eq!(simplified, CExpr::IntLit(0));
    }

    #[test]
    fn test_identity_mul_one() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::Mul,
            CExpr::Var("x".to_string()),
            CExpr::IntLit(1),
            Some(4),
        );
        assert_eq!(simplified, CExpr::Var("x".to_string()));
    }

    #[test]
    fn test_identity_div_one() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::Div,
            CExpr::Var("x".to_string()),
            CExpr::IntLit(1),
            Some(4),
        );
        assert_eq!(simplified, CExpr::Var("x".to_string()));
    }

    #[test]
    fn test_identity_and_all_ones_with_explicit_width() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::BitAnd,
            CExpr::Var("x".to_string()),
            CExpr::UIntLit(0xffff_ffff),
            Some(4),
        );
        assert_eq!(simplified, CExpr::Var("x".to_string()));
    }

    #[test]
    fn test_identity_negative_cases_preserved() {
        let ctx = FoldingContext::new(64);
        let sub = ctx.identity_simplify_binary(
            BinaryOp::Sub,
            CExpr::Var("x".to_string()),
            CExpr::IntLit(1),
            Some(4),
        );
        assert_eq!(
            sub,
            CExpr::binary(BinaryOp::Sub, CExpr::Var("x".to_string()), CExpr::IntLit(1))
        );

        let add = ctx.identity_simplify_binary(
            BinaryOp::Add,
            CExpr::Var("x".to_string()),
            CExpr::IntLit(2),
            Some(4),
        );
        assert_eq!(
            add,
            CExpr::binary(BinaryOp::Add, CExpr::Var("x".to_string()), CExpr::IntLit(2))
        );

        let or = ctx.identity_simplify_binary(
            BinaryOp::BitOr,
            CExpr::Var("x".to_string()),
            CExpr::IntLit(1),
            Some(4),
        );
        assert_eq!(
            or,
            CExpr::binary(
                BinaryOp::BitOr,
                CExpr::Var("x".to_string()),
                CExpr::IntLit(1)
            )
        );
    }

    #[test]
    fn test_noop_assignment_is_suppressed() {
        let ctx = FoldingContext::new(64);
        let lhs = CExpr::Var("x".to_string());
        let rhs = CExpr::binary(BinaryOp::Sub, CExpr::Var("x".to_string()), CExpr::IntLit(0));
        let stmt = ctx.assign_stmt(lhs, rhs);
        assert!(stmt.is_none(), "x = x - 0 should be suppressed as a no-op");
    }

    #[test]
    fn test_rewrite_stack_deref_to_external_name() {
        let mut ctx = FoldingContext::new(64);
        let mut external = HashMap::new();
        external.insert(
            -64,
            stack_var_spec(
                "buf",
                Some(CType::Array(Box::new(CType::Int(8)), Some(64))),
                Some("RBP"),
            ),
        );
        ctx.set_external_stack_vars(external);
        ctx.analyze_blocks(&[]);

        let expr = CExpr::Deref(Box::new(CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("rbp_1".to_string()),
            CExpr::IntLit(-0x40),
        )));

        assert_eq!(ctx.rewrite_stack_expr(expr), CExpr::Var("buf".to_string()));
    }

    #[test]
    fn test_rewrite_stack_address_expr_for_call_arg() {
        let mut ctx = FoldingContext::new(64);
        let mut external = HashMap::new();
        external.insert(-64, stack_var_spec("buf", None, Some("RBP")));
        ctx.set_external_stack_vars(external);
        ctx.analyze_blocks(&[]);

        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("rbp_1".to_string()),
            CExpr::IntLit(-0x40),
        );
        assert_eq!(ctx.rewrite_stack_expr(expr), CExpr::Var("buf".to_string()));
    }

    #[test]
    fn test_rewrite_stack_cast_paren_expr() {
        let mut ctx = FoldingContext::new(64);
        let mut external = HashMap::new();
        external.insert(
            -72,
            stack_var_spec("user_input", Some(CType::ptr(CType::Int(8))), Some("RBP")),
        );
        ctx.set_external_stack_vars(external);
        ctx.analyze_blocks(&[]);

        let expr = CExpr::Deref(Box::new(CExpr::Cast {
            ty: CType::ptr(CType::Int(8)),
            expr: Box::new(CExpr::Paren(Box::new(CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("rbp_1".to_string()),
                CExpr::IntLit(-0x48),
            )))),
        }));

        assert_eq!(
            ctx.rewrite_stack_expr(expr),
            CExpr::Var("user_input".to_string())
        );
    }

    #[test]
    fn test_rewrite_stack_unknown_offset_preserved() {
        let mut ctx = FoldingContext::new(64);
        let mut external = HashMap::new();
        external.insert(-64, stack_var_spec("buf", None, Some("RBP")));
        ctx.set_external_stack_vars(external);
        ctx.analyze_blocks(&[]);

        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("rbp_1".to_string()),
            CExpr::IntLit(-0x20),
        );
        assert_eq!(ctx.rewrite_stack_expr(expr.clone()), expr);
    }

    #[test]
    fn test_resolve_stack_var_canonicalizes_local_name_using_external_offset_mirror() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .stack_info
            .stack_vars
            .insert(4, "local_4".to_string());
        ctx.set_external_stack_vars(HashMap::from([(
            -4,
            stack_var_spec("result", None, Some("RBP")),
        )]));

        assert_eq!(ctx.resolve_stack_var(4), Some("result".to_string()));
    }

    #[test]
    fn test_resolve_stack_var_prefers_semantic_offset_zero_alias_over_stack_placeholder() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .stack_info
            .stack_vars
            .insert(0, "stack_0".to_string());
        ctx.set_external_stack_vars(HashMap::from([(
            0,
            stack_var_spec("saved_rbp", None, Some("RBP")),
        )]));

        assert_eq!(ctx.resolve_stack_var(0), Some("saved_rbp".to_string()));
    }

    #[test]
    fn test_resolve_stack_var_does_not_render_reserved_param_stack_home_alias() {
        let mut ctx = FoldingContext::new(64);
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([(
            "rdi".to_string(),
            "a".to_string(),
        )])));
        ctx.state
            .analysis_ctx
            .stack_info
            .stack_vars
            .insert(-8, "a".to_string());

        assert_eq!(ctx.resolve_stack_var(-8), Some("local_8".to_string()));
    }

    #[test]
    fn test_var_name_canonicalizes_stack_alias_from_external_offset_mirror() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert("tmp:1_1".to_string(), "local_4".to_string());
        ctx.set_external_stack_vars(HashMap::from([(
            -4,
            stack_var_spec("result", None, Some("RBP")),
        )]));

        let rendered = ctx.var_name(&make_var("tmp:1", 1, 8));
        assert_eq!(rendered, "result");
    }

    #[test]
    fn test_condition_var_chain_resolves_stack_alias() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .stack_info
            .stack_vars
            .insert(-4, "value".to_string());
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "tmp:cond_1".to_string(),
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var("result".to_string()),
                    CExpr::IntLit(25),
            ),
        );
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "result".to_string(),
            CExpr::Deref(Box::new(CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("rbp_1".to_string()),
                CExpr::IntLit(-4),
            ))),
        );

        let cond = ctx.get_condition_expr(&make_var("tmp:cond", 1, 1));
        let mut reads = HashSet::new();
        ctx.collect_expr_reads(&cond, &mut reads);
        assert!(
            reads.contains("value"),
            "Condition should resolve var-chain stack alias into canonical stack name"
        );
        assert!(
            !reads.contains("result"),
            "Condition should not keep intermediate non-canonical alias"
        );
    }

    #[test]
    fn test_condition_var_chain_resolves_stack_alias_through_cast_paren() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .stack_info
            .stack_vars
            .insert(-4, "value".to_string());
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "tmp:cond_1".to_string(),
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var("result".to_string()),
                CExpr::IntLit(19),
            ),
        );
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "result".to_string(),
            CExpr::Paren(Box::new(CExpr::Cast {
                ty: CType::ptr(CType::Int(32)),
                expr: Box::new(CExpr::Deref(Box::new(CExpr::Paren(Box::new(
                    CExpr::binary(
                        BinaryOp::Add,
                        CExpr::Var("rbp_1".to_string()),
                        CExpr::IntLit(-4),
                    ),
                ))))),
            })),
        );

        let cond = ctx.get_condition_expr(&make_var("tmp:cond", 1, 1));
        let mut reads = HashSet::new();
        ctx.collect_expr_reads(&cond, &mut reads);
        assert!(
            reads.contains("value"),
            "Cast/paren wrapped condition chain should still resolve stack alias"
        );
    }

    #[test]
    fn test_condition_var_chain_non_stack_remains_unforced() {
        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "tmp:cond_1".to_string(),
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var("result".to_string()),
                CExpr::IntLit(19),
            ),
        );
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "result".to_string(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("arg1".to_string()),
                CExpr::IntLit(1),
            ),
        );

        let cond = ctx.get_condition_expr(&make_var("tmp:cond", 1, 1));
        let mut reads = HashSet::new();
        ctx.collect_expr_reads(&cond, &mut reads);
        assert!(
            reads.contains("result"),
            "Non-stack var chains should not be force-rewritten"
        );
    }

    #[test]
    fn test_lookup_definition_resolves_formatted_temp_aliases() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("tmp:foo_2".to_string(), CExpr::Var("local_4".to_string()));
        ctx.state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert("tmp:foo_2".to_string(), "t2".to_string());

        let resolved = ctx.lookup_definition("t2");
        assert_eq!(resolved, Some(CExpr::Var("local_4".to_string())));
    }

    #[test]
    fn test_lookup_definition_resolves_hex_temp_alias_without_explicit_var_alias() {
        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "tmp:11f80_19".to_string(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::UIntLit(0x100002000),
                CExpr::IntLit(0x638),
            ),
        );

        let resolved = ctx.lookup_definition("t11f80_19");
        assert_eq!(
            resolved,
            Some(CExpr::binary(
                BinaryOp::Add,
                CExpr::UIntLit(0x100002000),
                CExpr::IntLit(0x638)
            ))
        );
    }

    #[test]
    fn lowered_alias_lookup_filters_raw_temporaries_with_typed_kind() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("tmp:raw_2".to_string(), CExpr::IntLit(1));
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("value_2".to_string(), CExpr::IntLit(2));
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("TMP:raw_2".to_string(), CExpr::IntLit(3));

        let temp_matches = ctx.ssa_names_for_lowered_temp_alias("t2");
        assert!(temp_matches.contains(&"tmp:raw_2".to_string()), "{temp_matches:?}");
        assert!(!temp_matches.contains(&"value_2".to_string()), "{temp_matches:?}");

        let value_matches = ctx.ssa_names_for_lowered_temp_alias("v2");
        assert!(value_matches.contains(&"value_2".to_string()), "{value_matches:?}");
        assert!(value_matches.contains(&"TMP:raw_2".to_string()), "{value_matches:?}");
        assert!(!value_matches.contains(&"tmp:raw_2".to_string()), "{value_matches:?}");
    }

    #[test]
    fn test_lookup_definition_prefers_forwarded_semantic_value_over_register_artifact() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("tmp:ret_1".to_string(), CExpr::Var("rax_2".to_string()));
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("src_1".to_string(), CExpr::Var("arg1".to_string()));
        ctx.state.analysis_ctx.use_info.forwarded_values.insert(
            "tmp:ret_1".to_string(),
            crate::analysis::ValueProvenance {
                source: "src_1".to_string(),
                source_value_id: None,
                source_var: None,
                stack_slot: None,
            },
        );

        let resolved = ctx.lookup_definition("tmp:ret_1");
        assert_eq!(resolved, Some(CExpr::Var("arg1".to_string())));
    }

    #[test]
    fn test_sf_surrogate_cycle_is_guarded() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("sf_1".to_string(), CExpr::Var("sf_2".to_string()));
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("sf_2".to_string(), CExpr::Var("sf_1".to_string()));

        assert!(
            !ctx.is_sf_surrogate(&CExpr::Var("sf_1".to_string())),
            "Cyclic surrogate definitions must short-circuit without recursion overflow"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_removes_unused_pure_copy() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("t1_1".to_string()),
                CExpr::Var("arg1".to_string()),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("t2_2".to_string()),
                CExpr::Var("arg2".to_string()),
            )),
            CStmt::Return(Some(CExpr::Var("t2_2".to_string()))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);
        assert_eq!(pruned.len(), 2, "Unused pure temp copy should be removed");
        assert!(
            !matches!(
                pruned.first(),
                Some(CStmt::Expr(CExpr::Binary {
                    op: BinaryOp::Assign,
                    left,
                    right: _,
                })) if left.as_ref() == &CExpr::Var("t1_1".to_string())
            ),
            "t1_1 copy should be pruned"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_removes_sleigh_load_store_temps() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("tmp_ldxn_1".to_string()),
                CExpr::Var("sym._debug_iomalloc_size".to_string()),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("tmp_stxn_1".to_string()),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("sym._debug_iomalloc_size".to_string()),
                    CExpr::Var("arg1".to_string()),
                ),
            )),
            CStmt::Return(Some(CExpr::Var("arg1".to_string()))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);

        assert_eq!(
            pruned,
            vec![CStmt::Return(Some(CExpr::Var("arg1".to_string())))]
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_removes_sleigh_memory_temps_with_call_address_artifacts() {
        let ctx = FoldingContext::new(64);
        let call_based_addr = CExpr::binary(
            BinaryOp::Add,
            CExpr::call(CExpr::Var("fcn.1000".to_string()), vec![CExpr::Var("ctx".to_string())]),
            CExpr::IntLit(50),
        );
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("tmp_ldwn_1".to_string()),
                CExpr::deref(call_based_addr.clone()),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("tmp_stwn_1".to_string()),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::deref(call_based_addr),
                    CExpr::Var("arg1".to_string()),
                ),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::deref(CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("x0_5".to_string()),
                    CExpr::IntLit(50),
                )),
                CExpr::Var("arg1".to_string()),
            )),
            CStmt::Return(Some(CExpr::Var("x0_5".to_string()))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);

        assert_eq!(pruned.len(), 2, "{pruned:?}");
        assert!(
            !format!("{:?}", pruned).contains("tmp_"),
            "dead Sleigh memory temps should not survive final output: {pruned:?}"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_keeps_dead_transient_call_as_side_effect() {
        let mut ctx = make_aarch64_ctx();
        ctx.set_known_function_signatures(HashMap::from([(
            "sym._IORWLockUnlock".to_string(),
            FunctionType {
                return_type: CType::Void,
                params: vec![CType::ptr(CType::Void)],
                variadic: false,
            },
        )]));
        let call = CExpr::call(
            CExpr::Var("sym._IORWLockUnlock".to_string()),
            vec![CExpr::Subscript {
                base: Box::new(CExpr::UIntLit(0xfffffe0007d21000)),
                index: Box::new(CExpr::IntLit(367)),
            }],
        );
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("x0_8".to_string()),
                call.clone(),
            )),
            CStmt::Return(Some(CExpr::Var("x0_3".to_string()))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);

        assert_eq!(
            pruned,
            vec![
                CStmt::Expr(call),
                CStmt::Return(Some(CExpr::Var("x0_3".to_string()))),
            ]
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_drops_dead_replayed_call_result() {
        let mut ctx = make_aarch64_ctx();
        let source_call = (0x1000, 0);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["x0_3".to_string(), "x0_4".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("x0_3".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("x0_4".to_string(), source_call);
        let call = CExpr::call(CExpr::Var("fcn.1000".to_string()), vec![CExpr::IntLit(16)]);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("x0_3".to_string()),
                call.clone(),
            )),
            CStmt::Expr(CExpr::assign(CExpr::Var("x0_4".to_string()), call)),
            CStmt::Return(Some(CExpr::Var("x0_3".to_string()))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);

        assert_eq!(
            pruned,
            vec![
                CStmt::Expr(CExpr::assign(
                    CExpr::Var("x0_3".to_string()),
                    CExpr::call(CExpr::Var("fcn.1000".to_string()), vec![CExpr::IntLit(16)]),
                )),
                CStmt::Return(Some(CExpr::Var("x0_3".to_string()))),
            ]
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_drops_duplicate_bare_replayed_call() {
        let mut ctx = make_aarch64_ctx();
        let source_call = (0x1000, 0);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["x0_3".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("x0_3".to_string(), source_call);
        let call = CExpr::call(CExpr::Var("fcn.1000".to_string()), vec![CExpr::IntLit(16)]);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("x0_3".to_string()),
                call.clone(),
            )),
            CStmt::Expr(call.clone()),
            CStmt::Expr(call),
            CStmt::Return(Some(CExpr::Var("x0_3".to_string()))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);

        assert_eq!(
            pruned,
            vec![
                CStmt::Expr(CExpr::assign(
                    CExpr::Var("x0_3".to_string()),
                    CExpr::call(CExpr::Var("fcn.1000".to_string()), vec![CExpr::IntLit(16)]),
                )),
                CStmt::Return(Some(CExpr::Var("x0_3".to_string()))),
            ]
        );
    }

    #[test]
    fn opaque_public_call_arg_sanitizer_hides_raw_tmp_names() {
        let ctx = make_aarch64_ctx();
        let callee = CExpr::Var("fcn.1000".to_string());

        let normalized =
            ctx.normalize_call_arg_expr_for_callee(&callee, CExpr::Var("tmp:2a000".to_string()));

        assert_eq!(normalized, CExpr::Var("value_2a000".to_string()));

        let normalized =
            ctx.normalize_call_arg_expr_for_callee(&callee, CExpr::Var("TMP:2A000".to_string()));

        assert_eq!(normalized, CExpr::Var("value_2a000".to_string()));

        let normalized =
            ctx.normalize_call_arg_expr_for_callee(&callee, CExpr::Var("visible_arg".to_string()));

        assert_eq!(normalized, CExpr::Var("visible_arg".to_string()));
    }

    #[test]
    fn test_propagate_ephemeral_copies_inlines_autogenerated_stack_home_param_copy() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("local_10".to_string()),
                CExpr::Var("v".to_string()),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Member {
                    base: Box::new(CExpr::Subscript {
                        base: Box::new(CExpr::Var("arr".to_string())),
                        index: Box::new(CExpr::Var("idx".to_string())),
                    }),
                    member: "f_8".to_string(),
                },
                CExpr::Var("local_10".to_string()),
            )),
        ];

        let propagated = ctx.propagate_ephemeral_copies(stmts);
        let CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            right,
            ..
        }) = &propagated[1]
        else {
            panic!("expected member assignment after propagation");
        };
        assert_eq!(
            right.as_ref(),
            &CExpr::Var("v".to_string()),
            "autogenerated stack-home param copy should inline into the member store"
        );

        let pruned = ctx.prune_dead_temp_assignments(propagated);
        assert_eq!(
            pruned.len(),
            1,
            "inlined autogenerated stack-home copy should prune away"
        );
    }

    #[test]
    fn propagate_ephemeral_copies_does_not_reuse_alias_after_call() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("tmp:1".to_string()),
                CExpr::Var("global_value".to_string()),
            )),
            CStmt::Expr(CExpr::call(CExpr::Var("mutate_global".to_string()), vec![])),
            CStmt::Return(Some(CExpr::Var("tmp:1".to_string()))),
        ];

        let propagated = ctx.propagate_ephemeral_copies(stmts);

        assert_eq!(
            propagated,
            vec![
                CStmt::Expr(CExpr::assign(
                    CExpr::Var("tmp:1".to_string()),
                    CExpr::Var("global_value".to_string()),
                )),
                CStmt::Expr(CExpr::call(CExpr::Var("mutate_global".to_string()), vec![])),
                CStmt::Return(Some(CExpr::Var("tmp:1".to_string()))),
            ],
            "copy aliases must not be reused across side-effecting calls"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_keeps_side_effecting_rhs() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("t1_1".to_string()),
                CExpr::call(CExpr::Var("foo".to_string()), vec![]),
            )),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);
        assert_eq!(
            pruned.len(),
            2,
            "Dead temp assignment must be kept when RHS has side effects"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_in_stmt_prunes_dead_structured_temp() {
        let ctx = FoldingContext::new(64);
        let stmt = CStmt::Block(vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("t3ea00".to_string()),
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::Var("len".to_string()),
                    CExpr::IntLit(64),
                ),
            )),
            CStmt::If {
                cond: CExpr::binary(
                    BinaryOp::Gt,
                    CExpr::Var("len".to_string()),
                    CExpr::IntLit(100),
                ),
                then_body: Box::new(CStmt::Return(Some(CExpr::IntLit(-1)))),
                else_body: Some(Box::new(CStmt::Return(Some(CExpr::IntLit(-2))))),
            },
        ]);

        let pruned = ctx.prune_dead_temp_assignments_in_stmt(stmt);
        let CStmt::Block(stmts) = pruned else {
            panic!("expected structured block after pruning");
        };
        assert_eq!(
            stmts.len(),
            1,
            "dead temp assignment that only survived until structured predicate lowering should be pruned"
        );
        assert!(
            matches!(stmts[0], CStmt::If { .. }),
            "structured conditional should remain after dead temp pruning"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_removes_dead_register_ssa_assignment() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("rax_6".to_string()),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("rax_3".to_string()),
                    CExpr::IntLit(1),
                ),
            )),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);
        assert_eq!(
            pruned.len(),
            1,
            "Dead pure assignment to SSA register artifact should be removed"
        );
        assert!(
            matches!(pruned[0], CStmt::Return(_)),
            "Return should be retained"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_keeps_dead_register_ssa_assignment_with_call_rhs() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("rax_6".to_string()),
                CExpr::call(CExpr::Var("foo".to_string()), vec![]),
            )),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);
        assert_eq!(
            pruned.len(),
            2,
            "Assignment with side-effecting RHS should not be pruned"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_removes_dead_flag_artifacts() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("tmpng_1".to_string()),
                CExpr::binary(BinaryOp::Lt, CExpr::Var("sp".to_string()), CExpr::IntLit(0)),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("tmpzr_1".to_string()),
                CExpr::binary(BinaryOp::Eq, CExpr::Var("sp".to_string()), CExpr::IntLit(0)),
            )),
            CStmt::Return(Some(CExpr::Subscript {
                base: Box::new(CExpr::cast(
                    CType::ptr(CType::UInt(32)),
                    CExpr::Var("arg1".to_string()),
                )),
                index: Box::new(CExpr::Var("arg2".to_string())),
            })),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);
        assert_eq!(
            pruned.len(),
            1,
            "Dead pure flag/temp assignments should be removed from final output"
        );
        assert!(
            matches!(pruned[0], CStmt::Return(_)),
            "Return should be preserved after pruning dead flag artifacts"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_removes_dead_stack_artifacts() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("local_c".to_string()),
                CExpr::Var("arg2".to_string()),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("local_10".to_string()),
                CExpr::Var("arg3".to_string()),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("stack_8".to_string()),
                CExpr::Var("arg1".to_string()),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("stack".to_string()),
                CExpr::Var("arg2".to_string()),
            )),
            CStmt::Return(Some(CExpr::Subscript {
                base: Box::new(CExpr::cast(
                    CType::ptr(CType::UInt(32)),
                    CExpr::Var("arg1".to_string()),
                )),
                index: Box::new(CExpr::Var("arg2".to_string())),
            })),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);
        assert_eq!(
            pruned.len(),
            1,
            "Dead synthetic stack/local bindings should not leak into final output"
        );
        assert!(matches!(pruned[0], CStmt::Return(_)));
    }

    #[test]
    fn test_prune_dead_temp_assignments_removes_dead_arm64_register_assignment() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("x8".to_string()),
                CExpr::Member {
                    base: Box::new(CExpr::Var("arg1".to_string())),
                    member: "f_30".to_string(),
                },
            )),
            CStmt::Return(Some(CExpr::binary(
                BinaryOp::Add,
                CExpr::Member {
                    base: Box::new(CExpr::Var("arg1".to_string())),
                    member: "f_30".to_string(),
                },
                CExpr::Member {
                    base: Box::new(CExpr::Var("arg1".to_string())),
                    member: "f_0".to_string(),
                },
            ))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);
        assert_eq!(
            pruned.len(),
            1,
            "Dead arm64 register artifacts should not survive final output"
        );
        assert!(matches!(pruned[0], CStmt::Return(_)));
    }

    #[test]
    fn test_prune_dead_temp_assignments_keeps_dead_dotted_global_like_target() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("obj.global_counter".to_string()),
                CExpr::IntLit(1),
            )),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);
        assert_eq!(
            pruned.len(),
            2,
            "Dotted/global-like semantic bindings should not be pruned"
        );
    }

    #[test]
    fn test_propagate_ephemeral_copies_rewrites_phi_copy_residue() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("eax_2".to_string()),
                CExpr::Var("arg1".to_string()),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("eax_3".to_string()),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("eax_2".to_string()),
                    CExpr::Var("eax_2".to_string()),
                ),
            )),
            CStmt::Return(Some(CExpr::Var("eax_3".to_string()))),
        ];

        let propagated = ctx.propagate_ephemeral_copies(stmts);
        let Some((_, rhs)) = FoldingContext::assignment_target_and_rhs(&propagated[1]) else {
            panic!("expected assignment at propagated[1]");
        };
        let mut reads = HashSet::new();
        ctx.collect_expr_reads(rhs, &mut reads);
        assert!(
            reads.contains("arg1") && !reads.contains("eax_2"),
            "Copy-forward should substitute eax_2 uses with arg1"
        );

        let pruned = ctx.prune_dead_temp_assignments(propagated);
        assert!(
            !pruned.iter().any(|stmt| {
                matches!(
                    FoldingContext::assignment_target_and_rhs(stmt),
                    Some((target, _)) if target == "eax_2"
                )
            }),
            "Dead phi-copy assignment should be removed after propagation"
        );
    }

    #[test]
    fn test_propagate_ephemeral_copies_keeps_call_rhs_unsubstituted() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("eax_2".to_string()),
                CExpr::call(CExpr::Var("foo".to_string()), vec![]),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("eax_3".to_string()),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("eax_2".to_string()),
                    CExpr::IntLit(1),
                ),
            )),
        ];

        let propagated = ctx.propagate_ephemeral_copies(stmts);
        let Some((_, rhs)) = FoldingContext::assignment_target_and_rhs(&propagated[1]) else {
            panic!("expected assignment at propagated[1]");
        };
        let mut reads = HashSet::new();
        ctx.collect_expr_reads(rhs, &mut reads);
        assert!(
            reads.contains("eax_2"),
            "Call RHS should not be used for copy-forward substitution"
        );
    }

    #[test]
    fn normalize_final_stmt_calls_preserves_definition_root_imported_call_under_cast() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401190,
            "sym.imp.malloc".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.malloc".to_string(),
            FunctionType {
                return_type: CType::ptr(CType::Void),
                params: vec![CType::UInt(64)],
                variadic: false,
            },
        )]));

        let stmt = CStmt::Expr(CExpr::assign(
            CExpr::Var("var_10h".to_string()),
            CExpr::cast(
                CType::ptr(CType::Void),
                CExpr::call(
                    CExpr::Var("sym.imp.malloc".to_string()),
                    vec![CExpr::binary(
                        BinaryOp::Add,
                        CExpr::Var("len".to_string()),
                        CExpr::IntLit(1),
                    )],
                ),
            ),
        ));

        let normalized = ctx.normalize_final_stmt_calls(stmt);
        let Some((_, rhs)) = FoldingContext::assignment_target_and_rhs(&normalized) else {
            panic!("expected normalized assignment");
        };
        assert_eq!(
            rhs,
            &CExpr::cast(
                CType::ptr(CType::Void),
                CExpr::call(
                    CExpr::Var("sym.imp.malloc".to_string()),
                    vec![CExpr::binary(
                        BinaryOp::Add,
                        CExpr::Var("len".to_string()),
                        CExpr::IntLit(1),
                    )],
                ),
            ),
            "definition-root imported call under cast should stay a call, got {normalized:?}"
        );
    }

    #[test]
    fn test_propagate_ephemeral_copies_invalidates_alias_when_source_redefined() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("eax_2".to_string()),
                CExpr::Var("rdi_1".to_string()),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("rdi_1".to_string()),
                CExpr::IntLit(42),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("eax_3".to_string()),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("eax_2".to_string()),
                    CExpr::IntLit(1),
                ),
            )),
        ];

        let propagated = ctx.propagate_ephemeral_copies(stmts);
        let Some((_, rhs)) = FoldingContext::assignment_target_and_rhs(&propagated[2]) else {
            panic!("expected assignment at propagated[2]");
        };
        let mut reads = HashSet::new();
        ctx.collect_expr_reads(rhs, &mut reads);
        assert!(
            reads.contains("eax_2"),
            "Alias must be invalidated when its RHS source variable is reassigned"
        );
    }

    #[test]
    fn test_propagate_ephemeral_copies_tracks_cast_var_rhs() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("eax_2".to_string()),
                CExpr::Cast {
                    ty: CType::Int(64),
                    expr: Box::new(CExpr::Var("arg1".to_string())),
                },
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("eax_3".to_string()),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("eax_2".to_string()),
                    CExpr::IntLit(1),
                ),
            )),
        ];

        let propagated = ctx.propagate_ephemeral_copies(stmts);
        let Some((_, rhs)) = FoldingContext::assignment_target_and_rhs(&propagated[1]) else {
            panic!("expected assignment at propagated[1]");
        };
        assert!(
            matches!(
                rhs,
                CExpr::Binary {
                    left,
                    right: _,
                    op: BinaryOp::Add,
                } if matches!(left.as_ref(), CExpr::Cast { expr, .. } if matches!(expr.as_ref(), CExpr::Var(name) if name == "arg1"))
            ),
            "Cast(Var(...)) should be propagated as a cheap copy RHS"
        );
    }

    #[test]
    fn test_propagate_ephemeral_copies_keeps_semantic_member_base() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                CExpr::Var("tmp:base_1".to_string()),
                CExpr::Var("rdx_2".to_string()),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("eax_3".to_string()),
                CExpr::PtrMember {
                    base: Box::new(CExpr::Var("tmp:base_1".to_string())),
                    member: "third".to_string(),
                },
            )),
        ];

        let propagated = ctx.propagate_ephemeral_copies(stmts);
        let Some((_, rhs)) = FoldingContext::assignment_target_and_rhs(&propagated[1]) else {
            panic!("expected assignment at propagated[1]");
        };
        assert!(
            matches!(
                rhs,
                CExpr::PtrMember { base, .. }
                    if matches!(base.as_ref(), CExpr::Var(name) if name == "tmp:base_1")
            ),
            "copy propagation must not rewrite semantic member bases back into transient registers"
        );
    }

    #[test]
    fn test_copy_predicate_assignment_uses_simplified_rhs() {
        let edi_0 = make_var("EDI", 0, 4);
        let sub = make_var("tmp:9100", 1, 4);
        let zf_1 = make_var("ZF", 1, 1);
        let cond = make_var("tmp:9101", 1, 1);
        let const_0 = make_var("const:0", 0, 4);

        let block = make_block(vec![
            SSAOp::IntSub {
                dst: sub.clone(),
                a: edi_0,
                b: const_0.clone(),
            },
            SSAOp::IntEqual {
                dst: zf_1.clone(),
                a: sub,
                b: const_0,
            },
            SSAOp::BoolNot {
                dst: cond.clone(),
                src: zf_1,
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);
        let rhs = ctx.resolve_predicate_rhs_for_var(&cond, ctx.get_expr(&cond));

        assert!(
            expr_contains_binary_op(&rhs, BinaryOp::Ne),
            "Predicate copy helper should preserve high-level comparison form"
        );
        assert!(
            !expr_contains_flag_artifact(&rhs),
            "Predicate copy helper output should not contain raw flag temporaries"
        );
        assert!(
            !expr_contains_sub_zero_cmp_scaffold(&rhs),
            "Predicate copy helper output should not contain cmp-to-zero subtraction scaffold"
        );
    }

    #[test]
    fn test_predicate_cast_and_boolnot_assignment_preserve_source_expression() {
        let edi_0 = make_var("EDI", 0, 4);
        let cmp = make_var("tmp:9200", 1, 1);
        let casted = make_var("tmp:9201", 1, 4);
        let negated = make_var("tmp:9202", 1, 1);
        let const_0 = make_var("const:0", 0, 4);

        let block = make_block(vec![
            SSAOp::IntNotEqual {
                dst: cmp.clone(),
                a: edi_0,
                b: const_0,
            },
            SSAOp::IntZExt {
                dst: casted.clone(),
                src: cmp.clone(),
            },
            SSAOp::BoolNot {
                dst: negated.clone(),
                src: casted,
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);

        let cast_stmt = ctx
            .op_to_stmt(&block.ops[1])
            .expect("casted predicate assignment should lower");
        let Some((_, cast_rhs)) = FoldingContext::assignment_target_and_rhs(&cast_stmt) else {
            panic!("expected assignment statement for casted predicate");
        };
        assert!(
            expr_contains_binary_op(cast_rhs, BinaryOp::Ne),
            "Cast assignment should preserve the predicate comparison"
        );
        assert!(
            !matches!(cast_rhs, CExpr::IntLit(_) | CExpr::UIntLit(_)),
            "Predicate cast assignment must not collapse to a literal"
        );

        let negated_stmt = ctx
            .op_to_stmt(&block.ops[2])
            .expect("boolnot predicate assignment should lower");
        let Some((_, negated_rhs)) = FoldingContext::assignment_target_and_rhs(&negated_stmt)
        else {
            panic!("expected assignment statement for negated predicate");
        };
        assert!(
            ctx.is_assignment_predicate_expr(negated_rhs),
            "BoolNot assignment should still lower to a predicate expression"
        );
        assert!(
            !matches!(negated_rhs, CExpr::IntLit(_) | CExpr::UIntLit(_)),
            "Negated predicate assignment must not collapse to a literal"
        );
        assert!(
            !expr_contains_flag_artifact(negated_rhs),
            "BoolNot assignment should not reintroduce raw flag artifacts"
        );
    }

    #[test]
    fn test_copy_suppresses_entry_arg_alias_assignment() {
        let ctx = FoldingContext::new(64);
        let stmt = ctx.op_to_stmt(&SSAOp::Copy {
            dst: make_var("arg1", 0, 4),
            src: make_var("EDI", 0, 4),
        });
        assert!(
            stmt.is_none(),
            "arg1 = edi entry alias copy should be suppressed"
        );
    }

    #[test]
    fn test_copy_suppresses_uninitialized_return_register_phi_carrier() {
        let ctx = FoldingContext::new(64);
        let stmt = ctx.op_to_stmt(&SSAOp::Copy {
            dst: make_var("EAX", 1, 4),
            src: make_var("EAX", 0, 4),
        });
        assert!(
            stmt.is_none(),
            "version-0 return-register phi carriers should not render as source assignments"
        );

        let real_copy = ctx.op_to_stmt(&SSAOp::Copy {
            dst: make_var("EAX", 1, 4),
            src: make_var("EDI", 0, 4),
        });
        assert!(
            real_copy.is_some(),
            "only uninitialized return-register carriers should be suppressed"
        );
    }

    #[test]
    fn test_assign_stmt_suppresses_entry_arg_alias_assignment() {
        let ctx = FoldingContext::new(64);
        let stmt = ctx.assign_stmt(
            CExpr::Var("arg1".to_string()),
            CExpr::Var("edi".to_string()),
        );
        assert!(
            stmt.is_none(),
            "arg1 = edi should be suppressed even after non-copy normalization paths"
        );
    }

    #[test]
    fn test_simplify_signed_gt_from_ne_and_of_eq_sf() {
        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.flag_info.flag_origins.insert(
            "OF_1".to_string(),
            ("a".to_string(), "const:0_0".to_string()),
        );

        let expr = CExpr::binary(
            BinaryOp::And,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("a".to_string()), CExpr::IntLit(0)),
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var("of_1".to_string()),
                CExpr::binary(BinaryOp::Lt, CExpr::Var("a".to_string()), CExpr::IntLit(0)),
            ),
        );

        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Gt, CExpr::Var("a".to_string()), CExpr::IntLit(0))
        );
    }

    #[test]
    fn test_simplify_signed_gt_from_ne_and_of_eq_sf_with_casted_zero() {
        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.flag_info.flag_origins.insert(
            "OF_1".to_string(),
            ("a".to_string(), "const:0_0".to_string()),
        );

        let expr = CExpr::binary(
            BinaryOp::And,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("a".to_string()), CExpr::IntLit(0)),
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var("of_1".to_string()),
                CExpr::binary(
                    BinaryOp::Lt,
                    CExpr::cast(CType::Int(32), CExpr::Var("a".to_string())),
                    CExpr::cast(CType::Int(32), CExpr::IntLit(0)),
                ),
            ),
        );

        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Gt, CExpr::Var("a".to_string()), CExpr::IntLit(0))
        );
    }

    #[test]
    fn test_extract_flag_name_requires_strict_token_match() {
        let ctx = FoldingContext::new(64);
        assert_eq!(
            ctx.extract_of(&CExpr::Var("of_12".to_string())),
            Some("of_12".to_string())
        );
        assert_eq!(ctx.extract_of(&CExpr::Var("offset_1".to_string())), None);
        assert_eq!(ctx.extract_of(&CExpr::Var("proof".to_string())), None);
    }

    #[test]
    fn test_simplify_signed_ge_from_of_eq_sf() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .flag_info
            .flag_origins
            .insert("OF_2".to_string(), ("a".to_string(), "b".to_string()));

        let expr = CExpr::binary(
            BinaryOp::Eq,
            CExpr::Var("of_2".to_string()),
            CExpr::binary(
                BinaryOp::Lt,
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::Var("a".to_string()),
                    CExpr::Var("b".to_string()),
                ),
                CExpr::IntLit(0),
            ),
        );

        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Ge,
                CExpr::Var("a".to_string()),
                CExpr::Var("b".to_string())
            )
        );
    }

    #[test]
    fn test_simplify_signed_lt_from_of_ne_sf() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .flag_info
            .flag_origins
            .insert("OF_3".to_string(), ("a".to_string(), "b".to_string()));

        let expr = CExpr::binary(
            BinaryOp::Ne,
            CExpr::Var("of_3".to_string()),
            CExpr::binary(
                BinaryOp::Lt,
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::Var("a".to_string()),
                    CExpr::Var("b".to_string()),
                ),
                CExpr::IntLit(0),
            ),
        );

        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Lt,
                CExpr::Var("a".to_string()),
                CExpr::Var("b".to_string())
            )
        );
    }

    #[test]
    fn test_simplify_direct_zf_and_not_zf_from_compare_provenance() {
        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.flag_info.compare_provenance.insert(
            "ZF_7".to_string(),
            crate::analysis::FlagCompareProvenance {
                lhs: "result".to_string(),
                rhs: "25".to_string(),
                kind: crate::analysis::FlagCompareKind::Equality,
            },
        );

        let eq = ctx.simplify_condition_expr(CExpr::Var("zf_7".to_string()));
        let ne =
            ctx.simplify_condition_expr(CExpr::unary(UnaryOp::Not, CExpr::Var("zf_7".to_string())));

        assert_eq!(
            eq,
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var("result".to_string()),
                CExpr::IntLit(25)
            )
        );
        assert_eq!(
            ne,
            CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("result".to_string()),
                CExpr::IntLit(25)
            )
        );
    }

    #[test]
    fn test_simplify_unsigned_relations_from_cf_and_zf_provenance() {
        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.flag_info.compare_provenance.insert(
            "CF_1".to_string(),
            crate::analysis::FlagCompareProvenance {
                lhs: "x".to_string(),
                rhs: "10".to_string(),
                kind: crate::analysis::FlagCompareKind::UnsignedLess,
            },
        );
        ctx.state.analysis_ctx.flag_info.compare_provenance.insert(
            "ZF_1".to_string(),
            crate::analysis::FlagCompareProvenance {
                lhs: "x".to_string(),
                rhs: "10".to_string(),
                kind: crate::analysis::FlagCompareKind::Equality,
            },
        );

        let lt = ctx.simplify_condition_expr(CExpr::Var("cf_1".to_string()));
        let ge =
            ctx.simplify_condition_expr(CExpr::unary(UnaryOp::Not, CExpr::Var("cf_1".to_string())));
        let le = ctx.simplify_condition_expr(CExpr::binary(
            BinaryOp::Or,
            CExpr::Var("cf_1".to_string()),
            CExpr::Var("zf_1".to_string()),
        ));
        let gt = ctx.simplify_condition_expr(CExpr::binary(
            BinaryOp::And,
            CExpr::unary(UnaryOp::Not, CExpr::Var("cf_1".to_string())),
            CExpr::unary(UnaryOp::Not, CExpr::Var("zf_1".to_string())),
        ));

        assert_eq!(
            lt,
            CExpr::binary(BinaryOp::Lt, CExpr::Var("x".to_string()), CExpr::IntLit(10))
        );
        assert_eq!(
            ge,
            CExpr::binary(BinaryOp::Ge, CExpr::Var("x".to_string()), CExpr::IntLit(10))
        );
        assert_eq!(
            le,
            CExpr::binary(BinaryOp::Le, CExpr::Var("x".to_string()), CExpr::IntLit(10))
        );
        assert_eq!(
            gt,
            CExpr::binary(BinaryOp::Gt, CExpr::Var("x".to_string()), CExpr::IntLit(10))
        );
    }

    #[test]
    fn test_simplify_unsigned_relations_from_lifted_hex_const_compare_provenance() {
        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.flag_info.compare_provenance.insert(
            "CF_1".to_string(),
            crate::analysis::FlagCompareProvenance {
                lhs: "len".to_string(),
                rhs: "const:64_0".to_string(),
                kind: crate::analysis::FlagCompareKind::UnsignedLess,
            },
        );
        ctx.state.analysis_ctx.flag_info.compare_provenance.insert(
            "ZF_1".to_string(),
            crate::analysis::FlagCompareProvenance {
                lhs: "len".to_string(),
                rhs: "const:64_0".to_string(),
                kind: crate::analysis::FlagCompareKind::Equality,
            },
        );

        let le = ctx.simplify_condition_expr(CExpr::binary(
            BinaryOp::Or,
            CExpr::Var("cf_1".to_string()),
            CExpr::Var("zf_1".to_string()),
        ));
        let gt = ctx.simplify_condition_expr(CExpr::unary(
            UnaryOp::Not,
            CExpr::binary(
                BinaryOp::Or,
                CExpr::Var("cf_1".to_string()),
                CExpr::Var("zf_1".to_string()),
            ),
        ));

        assert_eq!(
            le,
            CExpr::binary(
                BinaryOp::Le,
                CExpr::Var("len".to_string()),
                CExpr::IntLit(100)
            )
        );
        assert_eq!(
            gt,
            CExpr::binary(
                BinaryOp::Gt,
                CExpr::Var("len".to_string()),
                CExpr::IntLit(100)
            )
        );
    }

    #[test]
    fn test_compare_flag_copy_chain_keeps_relation_and_not_tmp_scaffold() {
        let edi_0 = make_var("EDI", 0, 4);
        let sub = make_var("tmp:9300", 1, 4);
        let zf_1 = make_var("ZF", 1, 1);
        let alias = make_var("tmp:9301", 1, 1);
        let cond = make_var("tmp:9302", 1, 1);
        let const_25 = make_var("const:25", 0, 4);
        let const_0 = make_var("const:0", 0, 4);

        let block = make_block(vec![
            SSAOp::IntSub {
                dst: sub.clone(),
                a: edi_0,
                b: const_25,
            },
            SSAOp::IntEqual {
                dst: zf_1.clone(),
                a: sub,
                b: const_0,
            },
            SSAOp::Copy {
                dst: alias.clone(),
                src: zf_1,
            },
            SSAOp::BoolNot {
                dst: cond.clone(),
                src: alias,
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);
        let rhs = ctx.resolve_predicate_rhs_for_var(&cond, ctx.get_expr(&cond));

        assert_eq!(
            rhs,
            CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("arg1".to_string()),
                CExpr::IntLit(37)
            )
        );
        assert!(
            !expr_contains_flag_artifact(&rhs),
            "predicate copy chain should collapse to the recovered comparison"
        );
        assert!(
            !expr_contains_sub_zero_cmp_scaffold(&rhs),
            "predicate copy chain should not preserve cmp-zero subtraction scaffolds"
        );
    }

    #[test]
    fn test_signed_canonicalization_mismatch_does_not_collapse() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .flag_info
            .flag_origins
            .insert("OF_4".to_string(), ("a".to_string(), "b".to_string()));

        let expr = CExpr::binary(
            BinaryOp::And,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("x".to_string()), CExpr::IntLit(0)),
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var("of_4".to_string()),
                CExpr::binary(BinaryOp::Lt, CExpr::Var("y".to_string()), CExpr::IntLit(0)),
            ),
        );

        let simplified = ctx.simplify_condition_expr(expr.clone());
        assert!(
            matches!(
                simplified,
                CExpr::Binary {
                    op: BinaryOp::And,
                    ..
                }
            ),
            "Mismatched tuple should not collapse to a top-level signed relation"
        );
        assert!(
            !matches!(
                simplified,
                CExpr::Binary {
                    op: BinaryOp::Gt | BinaryOp::Ge | BinaryOp::Lt | BinaryOp::Le,
                    ..
                }
            ),
            "Mismatched tuple should remain conjunctive at top level"
        );
    }

    #[test]
    fn test_stack_prologue_arg_alias_recovery() {
        let rbp_1 = make_var("RBP", 1, 8);
        let edi_0 = make_var("EDI", 0, 4);
        let addr = make_var("tmp:7000", 1, 8);
        let arg_copy = make_var("tmp:7001", 1, 4);
        let loaded = make_var("tmp:7002", 1, 4);
        let cond = make_var("tmp:7003", 1, 1);
        let const_neg4 = make_var("const:fffffffffffffffc", 0, 8);
        let const_0 = make_var("const:0", 0, 4);

        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: addr.clone(),
                a: rbp_1.clone(),
                b: const_neg4,
            },
            SSAOp::Copy {
                dst: arg_copy.clone(),
                src: edi_0,
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: addr.clone(),
                val: arg_copy,
            },
            SSAOp::Load {
                dst: loaded.clone(),
                space: "ram".to_string(),
                addr,
            },
            SSAOp::IntNotEqual {
                dst: cond.clone(),
                a: loaded.clone(),
                b: const_0,
            },
            SSAOp::CBranch {
                cond,
                target: make_var("const:1000", 0, 8),
            },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_blocks(std::slice::from_ref(&block));

        assert_eq!(ctx.stack_vars_map().get(&-4), Some(&"arg1".to_string()));

        let mut visited = HashSet::new();
        let resolved =
            ctx.resolve_predicate_operand(&CExpr::Var(loaded.display_name()), 0, &mut visited);
        assert_eq!(resolved, CExpr::Var("arg1".to_string()));
    }

    #[test]
    fn stack_frame_op_uses_typed_temp_for_indirect_callee_saved_push() {
        let mut ctx = FoldingContext::new(64);
        let addr = make_var("tmp:stack", 1, 8);
        let saved = make_var("TMP:saved", 1, 8);
        ctx.state
            .analysis_ctx
            .use_info
            .copy_sources
            .insert(saved.display_name(), "RBX_1".to_string());

        assert!(ctx.is_stack_frame_op(&SSAOp::Store {
            space: "ram".to_string(),
            addr: addr.clone(),
            val: saved,
        }));
        assert!(!ctx.is_stack_frame_op(&SSAOp::Store {
            space: "ram".to_string(),
            addr,
            val: make_var("value", 1, 8),
        }));
    }

    #[test]
    fn local_branch_condition_does_not_inline_return_register_call_history() {
        let block = make_block(vec![
            SSAOp::Call {
                target: make_var("const:401000", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("EAX", 1, 4),
            },
            SSAOp::IntZExt {
                dst: make_var("RAX", 1, 8),
                src: make_var("EAX", 1, 4),
            },
            SSAOp::IntNotEqual {
                dst: make_var("tmp:pred", 1, 1),
                a: make_var("RAX", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::CBranch {
                cond: make_var("tmp:pred", 1, 1),
                target: make_var("const:1000", 0, 8),
            },
        ]);

        let mut ctx = make_x86_64_ctx();
        ctx.analyze_blocks(std::slice::from_ref(&block));

        let cond = ctx
            .extract_condition_from_block(&block)
            .expect("local branch condition");
        assert!(
            cond == CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("rax_1".to_string()),
                CExpr::IntLit(0),
            ) || matches!(
                cond,
                CExpr::Binary {
                    op: BinaryOp::Ne,
                    ref left,
                    ref right,
                } if matches!(left.as_ref(), CExpr::Call { .. })
                    && matches!(right.as_ref(), CExpr::IntLit(0))
            ),
            "expected local branch condition to stay a direct null-check without tmp scaffolding, got {cond:?}"
        );
    }

    #[test]
    fn aarch64_direct_call_result_materializes_callee_saved_owner_once() {
        let x0_ret = make_var("X0", 1, 8);
        let x20_owner = make_var("X20", 1, 8);
        let cond = make_var("tmp:pred", 1, 1);
        let block = make_block(vec![
            SSAOp::Call {
                target: make_var("const:401000", 0, 8),
            },
            SSAOp::CallDefine {
                dst: x0_ret.clone(),
            },
            SSAOp::Copy {
                dst: x20_owner.clone(),
                src: x0_ret,
            },
            SSAOp::IntEqual {
                dst: cond.clone(),
                a: x20_owner,
                b: make_var("const:0", 0, 8),
            },
            SSAOp::CBranch {
                cond: cond.clone(),
                target: make_var("const:2000", 0, 8),
            },
        ]);

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401000,
            "sym._kernel_helper".to_string(),
        )])));
        ctx.analyze_blocks(std::slice::from_ref(&block));
        let source_call = (block.addr, 0);
        assert!(
            ctx.should_materialize_call_result_at_source(source_call)
                .is_some(),
            "expected callee-saved call-result owner for source {:?}; aliases={:?}",
            source_call,
            ctx.call_result_aliases_map().get(&source_call)
        );
        let source_expr = ctx
            .call_result_exprs_map()
            .get(&source_call)
            .expect("source call expression")
            .clone();
        assert_eq!(ctx.source_call_for_call_expr(&source_expr), Some(source_call));
        assert_eq!(
            ctx.normalize_assignment_predicate_rhs(CExpr::binary(
                BinaryOp::Eq,
                source_expr,
                CExpr::IntLit(0),
            )),
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var("x20_1".to_string()),
                CExpr::IntLit(0),
            )
        );
        let pre_fold_branch_cond = ctx
            .extract_condition_from_block(&block)
            .expect("pre-fold local branch condition");
        assert_eq!(
            pre_fold_branch_cond,
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var("x20_1".to_string()),
                CExpr::IntLit(0),
            ),
            "expected pre-fold branch condition to reuse owned call result, got {pre_fold_branch_cond:?}"
        );

        let stmts = ctx.fold_block(&block, block.addr);
        let Some(CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        })) = stmts.first()
        else {
            panic!("expected call result owner assignment, got {stmts:?}");
        };
        assert_eq!(left.as_ref(), &CExpr::Var("x20_1".to_string()));
        assert!(
            matches!(right.as_ref(), CExpr::Call { .. }),
            "expected owner to materialize the call once, got {right:?}"
        );
        assert!(
            stmts.iter().skip(1).all(|stmt| {
                !matches!(
                    stmt,
                    CStmt::Expr(CExpr::Binary {
                        right,
                        ..
                    }) if matches!(right.as_ref(), CExpr::Call { .. })
                )
            }),
            "shadow call-result copies should be suppressed after call-site owner materialization: {stmts:?}"
        );

        let branch_cond = ctx
            .extract_condition_from_block(&block)
            .expect("local branch condition");
        assert_eq!(
            branch_cond,
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var("x20_1".to_string()),
                CExpr::IntLit(0),
            ),
            "expected branch condition to reuse owned call result, got {branch_cond:?}"
        );
    }

    #[test]
    fn aarch64_second_call_result_condition_does_not_reuse_prior_owner() {
        let first_ret = make_var("X0", 1, 8);
        let first_owner = make_var("X20", 1, 8);
        let second_ret = make_var("X0", 2, 8);
        let second_owner = make_var("X8", 1, 8);
        let restored_ret = make_var("X0", 3, 8);
        let cond = make_var("tmp:pred", 1, 1);
        let block = make_block(vec![
            SSAOp::Call {
                target: make_var("const:401000", 0, 8),
            },
            SSAOp::CallDefine {
                dst: first_ret.clone(),
            },
            SSAOp::Copy {
                dst: first_owner.clone(),
                src: first_ret,
            },
            SSAOp::Call {
                target: make_var("const:402000", 0, 8),
            },
            SSAOp::CallDefine {
                dst: second_ret.clone(),
            },
            SSAOp::Copy {
                dst: second_owner.clone(),
                src: second_ret,
            },
            SSAOp::Copy {
                dst: restored_ret,
                src: first_owner.clone(),
            },
            SSAOp::IntEqual {
                dst: cond.clone(),
                a: second_owner.clone(),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::CBranch {
                cond: cond.clone(),
                target: make_var("const:2000", 0, 8),
            },
        ]);

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x401000, "sym._first_helper".to_string()),
            (0x402000, "sym._second_helper".to_string()),
        ])));
        ctx.analyze_blocks(std::slice::from_ref(&block));

        assert_eq!(
            ctx.state
                .analysis_ctx
                .use_info
                .call_result_source_by_alias
                .get(&second_owner.display_name())
                .copied(),
            Some((block.addr, 3)),
            "x8 copy should remain owned by the second call; aliases={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias
        );

        let branch_cond = ctx
            .extract_condition_from_block(&block)
            .expect("local branch condition");
        assert_ne!(
            branch_cond,
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var(first_owner.display_name().to_ascii_lowercase()),
                CExpr::IntLit(0),
            ),
            "second-call null check must not collapse to the first call owner"
        );
        assert!(
            branch_cond == CExpr::binary(
                BinaryOp::Eq,
                CExpr::Var(second_owner.display_name().to_ascii_lowercase()),
                CExpr::IntLit(0),
            ) || matches!(
                branch_cond,
                CExpr::Binary {
                    op: BinaryOp::Eq,
                    ref left,
                    ref right,
                } if matches!(left.as_ref(), CExpr::Call { .. })
                    && right.as_ref() == &CExpr::IntLit(0)
            ),
            "expected branch condition to use the second call result, got {branch_cond:?}; second_expr={:?}; cond_expr={:?}; aliases={:?}; defs={:?}; formatted={:?}; semantic={:?}; var_aliases={:?}; copy_sources={:?}",
            ctx.get_expr(&second_owner),
            ctx.get_expr(&cond),
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state.analysis_ctx.use_info.definitions,
            ctx.state.analysis_ctx.use_info.formatted_defs,
            ctx.state.analysis_ctx.use_info.semantic_values,
            ctx.state.analysis_ctx.use_info.var_aliases,
            ctx.state.analysis_ctx.use_info.copy_sources
        );
        assert_ne!(
            ctx.get_expr(&second_owner),
            CExpr::Var("arg1".to_string()),
            "second call owner expression must not resolve to entry arg; expr={:?}; cond_expr={:?}; defs={:?}; formatted={:?}; semantic={:?}; aliases={:?}; copy_sources={:?}",
            ctx.get_expr(&second_owner),
            ctx.get_expr(&cond),
            ctx.state.analysis_ctx.use_info.definitions,
            ctx.state.analysis_ctx.use_info.formatted_defs,
            ctx.state.analysis_ctx.use_info.semantic_values,
            ctx.state.analysis_ctx.use_info.var_aliases,
            ctx.state.analysis_ctx.use_info.copy_sources
        );
    }

    #[test]
    fn prepared_aarch64_second_call_result_condition_uses_post_call_copy() {
        let arch = make_test_arch_aarch64_kernel_regs();
        let mut entry = R2ILBlock::new(0x1000, 0x18);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x4000, 8),
            src: Varnode::constant(0x111, 8),
        });
        entry.push(R2ILOp::IntAdd {
            dst: Varnode::register(0x40f0, 8),
            a: Varnode::constant(0x1004, 8),
            b: Varnode::constant(4, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::ram(0x401000, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x40a0, 8),
            src: Varnode::register(0x4000, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x4000, 8),
            src: Varnode::constant(0, 8),
        });
        entry.push(R2ILOp::IntAdd {
            dst: Varnode::register(0x40f0, 8),
            a: Varnode::constant(0x1008, 8),
            b: Varnode::constant(4, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::ram(0x402000, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x4040, 8),
            src: Varnode::register(0x4000, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x4000, 8),
            src: Varnode::register(0x40a0, 8),
        });
        entry.push(R2ILOp::IntEqual {
            dst: Varnode::unique(0x18f80, 1),
            a: Varnode::register(0x4040, 8),
            b: Varnode::constant(0, 8),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1020, 8),
            cond: Varnode::unique(0x18f80, 1),
        });
        let mut fallthrough = R2ILBlock::new(0x1018, 4);
        fallthrough.push(R2ILOp::Return {
            target: Varnode::register(0x4000, 8),
        });
        let mut taken = R2ILBlock::new(0x1020, 4);
        taken.push(R2ILOp::Return {
            target: Varnode::register(0x4000, 8),
        });

        let prepared =
            prepared_from_r2il_blocks(&[entry, fallthrough, taken], &arch).with_name("kernel_copy");
        let mut ctx = make_aarch64_ctx_with_prepared(&prepared);
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x401000, "sym._first_helper".to_string()),
            (0x402000, "sym._second_helper".to_string()),
        ])));
        let entry = prepared.function().get_block(0x1000).expect("entry");
        ctx.analyze_blocks(std::slice::from_ref(entry));
        let SSAOp::CBranch { cond, .. } = entry.ops.last().expect("last op") else {
            panic!("expected branch");
        };
        let prepared_candidate =
            ctx.prepared_predicate_candidate_for_branch_block_for_test(entry.addr, cond);
        let second_source = ctx
            .state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .get("X8_3")
            .copied();
        let second_owner = second_source
            .and_then(|source| ctx.stable_owned_call_result_name_for_source(source));

        let condition = ctx
            .extract_condition_from_block(entry)
            .expect("prepared branch condition");
        let rendered = format!("{condition:?}");
        assert_eq!(
            second_owner.as_deref(),
            Some("w10_2"),
            "expected x8 post-call copy to resolve to the second call owner"
        );
        assert!(
            !rendered.contains("x20")
                && !rendered.contains("X20")
                && !rendered.contains("w10_1")
                && !rendered.contains("sym._first_helper")
                && !matches!(
                    &condition,
                    CExpr::Binary { left, .. }
                        if matches!(
                            left.as_ref(),
                            CExpr::Var(name)
                                if name == "arg1" || name.eq_ignore_ascii_case("x0")
                        )
                ),
            "prepared predicate should use the second call result, not the restored first-call owner: {condition:?}; prepared_candidate={prepared_candidate:?}; second_source={second_source:?}; second_owner={second_owner:?}",
        );
    }

    #[test]
    fn prepared_aarch64_tbz_loaded_w8_does_not_reuse_prior_call_owner() {
        let arch = make_test_arch_aarch64_kernel_regs();
        let mut entry = R2ILBlock::new(0x2000, 0x20);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x4000, 8),
            src: Varnode::constant(0x111, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::ram(0x401000, 8),
        });
        entry.push(R2ILOp::Load {
            dst: Varnode::unique(0x25500, 1),
            space: SpaceId::Ram,
            addr: Varnode::ram(0x5000, 8),
        });
        entry.push(R2ILOp::IntZExt {
            dst: Varnode::register(0x4040, 8),
            src: Varnode::unique(0x25500, 1),
        });
        entry.push(R2ILOp::IntRight {
            dst: Varnode::unique(0x18900, 4),
            a: Varnode::register(0x4040, 4),
            b: Varnode::constant(0, 4),
        });
        entry.push(R2ILOp::IntAnd {
            dst: Varnode::unique(0x18980, 4),
            a: Varnode::unique(0x18900, 4),
            b: Varnode::constant(1, 4),
        });
        entry.push(R2ILOp::IntEqual {
            dst: Varnode::unique(0x18a80, 1),
            a: Varnode::unique(0x18980, 4),
            b: Varnode::constant(0, 4),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x2020, 8),
            cond: Varnode::unique(0x18a80, 1),
        });
        let mut fallthrough = R2ILBlock::new(0x2018, 4);
        fallthrough.push(R2ILOp::Return {
            target: Varnode::register(0x4000, 8),
        });
        let mut taken = R2ILBlock::new(0x2020, 4);
        taken.push(R2ILOp::Return {
            target: Varnode::register(0x4000, 8),
        });

        let prepared =
            prepared_from_r2il_blocks(&[entry, fallthrough, taken], &arch).with_name("kernel_tbz");
        let mut ctx = make_aarch64_ctx_with_prepared(&prepared);
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401000,
            "sym._first_helper".to_string(),
        )])));
        let entry = prepared.function().get_block(0x2000).expect("entry");
        ctx.analyze_blocks(std::slice::from_ref(entry));

        let condition = ctx
            .extract_condition_from_block(entry)
            .expect("tbz branch condition");
        let rendered = format!("{condition:?}");
        assert!(
            !rendered.contains("w10_1") && !rendered.contains("sym._first_helper"),
            "tbz on loaded w8 must not reuse the prior call owner: {condition:?}",
        );
    }

    #[test]
    fn unknown_internal_call_owner_tolerates_low_quality_kernel_arg_mismatch() {
        let mut ctx = make_aarch64_ctx();
        let source_call = (0x1000, 0);
        let source_expr = CExpr::call(
            CExpr::Var("fcn.1000".to_string()),
            vec![
                CExpr::Var("arg1".to_string()),
                CExpr::Var("arg2".to_string()),
                CExpr::Var("value_2a000".to_string()),
                CExpr::Member {
                    base: Box::new(CExpr::Var("class".to_string())),
                    member: "std".to_string(),
                },
            ],
        );
        let replay_expr = CExpr::call(
            CExpr::Var("fcn.1000".to_string()),
            vec![
                CExpr::Var("arg1".to_string()),
                CExpr::Var("arg2".to_string()),
                CExpr::Var("tmp:2a000".to_string()),
                CExpr::IntLit(0),
            ],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, source_expr);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .entry(source_call)
            .or_default()
            .insert("X0_3".to_string());
        ctx.state
            .analysis_ctx
            .use_info
            .direct_call_result_aliases
            .insert("X0_3".to_string());

        assert_eq!(
            ctx.stable_owned_call_result_expr_for_call_expr(&replay_expr),
            Some(CExpr::Var("x0_3".to_string()))
        );
        assert_eq!(
            ctx.normalize_final_return_expr_candidate(replay_expr),
            CExpr::Var("x0_3".to_string())
        );
    }

    #[test]
    fn imported_call_owner_stays_strict_for_low_quality_arg_mismatch() {
        let mut ctx = make_aarch64_ctx();
        let source_call = (0x1000, 0);
        let source_expr = CExpr::call(
            CExpr::Var("sym.imp.helper".to_string()),
            vec![
                CExpr::Var("arg1".to_string()),
                CExpr::Var("arg2".to_string()),
                CExpr::Var("value_2a000".to_string()),
                CExpr::Member {
                    base: Box::new(CExpr::Var("class".to_string())),
                    member: "std".to_string(),
                },
            ],
        );
        let replay_expr = CExpr::call(
            CExpr::Var("sym.imp.helper".to_string()),
            vec![
                CExpr::Var("arg1".to_string()),
                CExpr::Var("arg2".to_string()),
                CExpr::Var("tmp:2a000".to_string()),
                CExpr::IntLit(0),
            ],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, source_expr);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .entry(source_call)
            .or_default()
            .insert("X0_3".to_string());
        ctx.state
            .analysis_ctx
            .use_info
            .direct_call_result_aliases
            .insert("X0_3".to_string());

        assert_eq!(
            ctx.stable_owned_call_result_expr_for_call_expr(&replay_expr),
            None
        );
    }

    #[test]
    fn typed_callee_identity_controls_return_register_owner_policy() {
        let cases = [
            ("ram:401000_0", false),
            ("const:401000", false),
            ("sym.imp.helper", false),
            ("imp.helper", false),
            ("fcn.1000", true),
            ("sym.helper", true),
        ];

        for (idx, (callee, expected)) in cases.into_iter().enumerate() {
            let mut ctx = make_aarch64_ctx();
            let source_call = (0x1000 + idx as u64, 0);
            ctx.state
                .analysis_ctx
                .use_info
                .call_result_exprs
                .insert(source_call, CExpr::call(CExpr::Var(callee.to_string()), vec![]));

            assert_eq!(
                ctx.source_call_allows_return_register_owner(source_call),
                expected,
                "{callee}",
            );
        }

        let mut ctx = make_aarch64_ctx();
        let source_call = (0x2000, 0);
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.helper".to_string(),
            FunctionType {
                return_type: CType::u64(),
                params: Vec::new(),
                variadic: false,
            },
        )]));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(
                source_call,
                CExpr::call(CExpr::Var("sym.helper".to_string()), vec![]),
            );

        assert!(
            !ctx.source_call_allows_return_register_owner(source_call),
            "known-signature callees already have typed return facts and must not fall back to return-register ownership",
        );
    }

    #[test]
    fn typed_callee_identity_controls_imported_call_policy() {
        let mut ctx = make_aarch64_ctx();
        assert!(ctx.is_imported_call_target(&CExpr::Var(
            "sym.imp.printf".to_string()
        )));
        assert!(ctx.is_imported_call_target(&CExpr::Var(
            "imp.printf".to_string()
        )));
        assert!(!ctx.is_imported_call_target(&CExpr::Var(
            "sym.helper".to_string()
        )));
        assert!(!ctx.is_imported_call_target(&CExpr::Var(
            "fcn.401000".to_string()
        )));

        ctx.set_known_function_signatures(HashMap::from([(
            "plain_helper".to_string(),
            FunctionType {
                return_type: CType::u64(),
                params: Vec::new(),
                variadic: false,
            },
        )]));

        assert!(!ctx.is_imported_call_target(&CExpr::Var(
            "plain_helper".to_string()
        )));
        assert!(!ctx.is_imported_call_target(&CExpr::Var(
            "other_helper".to_string()
        )));
    }

    #[test]
    fn identical_helper_replay_across_callsites_is_ambiguous() {
        let mut ctx = make_aarch64_ctx();
        let first_call = (0x1000, 0);
        let second_call = (0x1008, 0);
        let helper_call = CExpr::call(
            CExpr::Var("sym.imp.helper".to_string()),
            vec![CExpr::Var("arg1".to_string())],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(first_call, helper_call.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(second_call, helper_call.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(first_call, BTreeSet::from(["X20_1".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(second_call, BTreeSet::from(["X21_1".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .direct_call_result_aliases
            .extend(["X20_1".to_string(), "X21_1".to_string()]);
        ctx.state.analysis_ctx.ownership = ctx.build_semantic_ownership_facts();
        ctx.clear_semantic_ownership_caches();

        assert_eq!(ctx.source_call_for_call_expr(&helper_call), None);
        assert_eq!(
            ctx.stable_owned_call_result_expr_for_call_expr(&helper_call),
            None,
            "identical helper replay must not pick an arbitrary owner across callsites"
        );
    }

    #[test]
    fn test_use_info_deterministic() {
        let eax_0 = make_var("EAX", 0, 4);
        let tmp = make_var("tmp:8200", 1, 4);
        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: tmp.clone(),
                a: eax_0,
                b: make_var("const:1", 0, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("const:1000", 0, 8),
                val: tmp,
            },
        ]);

        let ctx_a = FoldingContext::new(64);
        let ctx_b = FoldingContext::new(64);
        let blocks = vec![block];

        let cfg_a = ctx_a.to_pass_env();
        let cfg_b = ctx_b.to_pass_env();
        let info_a = analysis::UseInfo::analyze(&blocks, &cfg_a);
        let info_b = analysis::UseInfo::analyze(&blocks, &cfg_b);
        assert_eq!(info_a, info_b, "UseInfo analysis should be deterministic");
    }

    #[test]
    fn test_flag_info_transitive_marking_and_guard() {
        let edi_0 = make_var("EDI", 0, 4);
        let tmp = make_var("tmp:8300", 1, 4);
        let zf_1 = make_var("ZF", 1, 1);
        let cond = make_var("tmp:8301", 1, 1);
        let const_0 = make_var("const:0", 0, 4);

        let flag_only_block = make_block(vec![
            SSAOp::IntSub {
                dst: tmp.clone(),
                a: edi_0.clone(),
                b: const_0.clone(),
            },
            SSAOp::IntEqual {
                dst: zf_1.clone(),
                a: tmp.clone(),
                b: const_0.clone(),
            },
            SSAOp::BoolNot {
                dst: cond.clone(),
                src: zf_1,
            },
            SSAOp::CBranch {
                cond,
                target: make_var("const:1000", 0, 8),
            },
        ]);

        let ctx = FoldingContext::new(64);
        let blocks = vec![flag_only_block];
        let cfg = ctx.to_pass_env();
        let use_info = analysis::UseInfo::analyze(&blocks, &cfg);
        let flag_info = analysis::FlagInfo::analyze(&blocks, &use_info, &cfg);
        assert!(flag_info.flag_only_values.contains(&tmp.display_name()));

        let tmp2 = make_var("tmp:8400", 1, 4);
        let zf_2 = make_var("ZF", 2, 1);
        let cond2 = make_var("tmp:8401", 1, 1);
        let guarded_block = make_block(vec![
            SSAOp::IntSub {
                dst: tmp2.clone(),
                a: edi_0,
                b: const_0.clone(),
            },
            SSAOp::IntEqual {
                dst: zf_2,
                a: tmp2.clone(),
                b: const_0,
            },
            SSAOp::BoolNot {
                dst: cond2.clone(),
                src: make_var("ZF", 2, 1),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("const:2000", 0, 8),
                val: tmp2.clone(),
            },
            SSAOp::CBranch {
                cond: cond2,
                target: make_var("const:1000", 0, 8),
            },
        ]);

        let ctx = FoldingContext::new(64);
        let blocks = vec![guarded_block];
        let cfg = ctx.to_pass_env();
        let use_info = analysis::UseInfo::analyze(&blocks, &cfg);
        let flag_info = analysis::FlagInfo::analyze(&blocks, &use_info, &cfg);
        assert!(!flag_info.flag_only_values.contains(&tmp2.display_name()));
    }

    #[test]
    fn test_stack_info_arg_alias_requires_version_zero() {
        let rbp_1 = make_var("RBP", 1, 8);
        let eax_1 = make_var("EAX", 1, 4);
        let addr = make_var("tmp:8500", 1, 8);
        let const_neg4 = make_var("const:fffffffffffffffc", 0, 8);
        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: addr.clone(),
                a: rbp_1,
                b: const_neg4,
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr,
                val: eax_1,
            },
        ]);

        let ctx = FoldingContext::new(64);
        let blocks = vec![block];
        let cfg = ctx.to_pass_env();
        let use_info = analysis::UseInfo::analyze(&blocks, &cfg);
        let stack_info = analysis::StackInfo::analyze(&blocks, &use_info, &cfg);

        assert!(
            !stack_info.stack_arg_aliases.values().any(|v| v == "arg1"),
            "Non-argument registers must not be treated as prologue arg aliases"
        );
    }

    #[test]
    fn test_analyze_function_structure_marks_exit_as_return_context() {
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let func = SSAFunction::from_blocks(&[block]).expect("SSA function should build");

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_function_structure(&func);

        assert!(ctx.state.return_blocks.contains(&0x1000));
    }

    #[test]
    fn annotate_stack_slot_semantics_keeps_scalar_return_kind_across_multiple_return_exits() {
        use r2il::R2ILBlock;
        use r2ssa::SSAFunction;

        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1008, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut early_return = R2ILBlock::new(0x1008, 4);
        early_return.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut scalar_path = R2ILBlock::new(0x1004, 4);
        scalar_path.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut final_exit = R2ILBlock::new(0x1010, 4);
        final_exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func =
            SSAFunction::from_blocks_raw_no_arch(&[entry, early_return, scalar_path, final_exit])
                .expect("ssa function");
        func = func.with_name("sym._multi_return_scalar_slot");

        func.get_block_mut(0x1000).expect("entry").ops = vec![SSAOp::CBranch {
            cond: make_var("tmp:cond", 1, 1),
            target: make_var("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1004).expect("scalar_path").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:retaddr", 1, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:retaddr", 1, 8),
                val: make_var("EDI", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1010", 0, 8),
            },
        ];
        func.get_block_mut(0x1008).expect("early_return").ops = vec![SSAOp::Return {
            target: make_var("RIP", 1, 8),
        }];
        func.get_block_mut(0x1010).expect("final_exit").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:retaddr", 2, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:retload", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:retaddr", 2, 8),
            },
            SSAOp::Copy {
                dst: make_var("EAX", 1, 4),
                src: make_var("tmp:retload", 1, 4),
            },
            SSAOp::IntZExt {
                dst: make_var("RAX", 1, 8),
                src: make_var("EAX", 1, 4),
            },
            SSAOp::Return {
                target: make_var("RIP", 2, 8),
            },
        ];

        let empty_u64 = Box::leak(Box::new(HashMap::new()));
        let empty_str = Box::leak(Box::new(HashMap::new()));
        let empty_ty = Box::leak(Box::new(HashMap::new()));
        let empty_saved = Box::leak(Box::new(HashSet::new()));
        let arg_regs = Box::leak(Box::new(vec![
            "rdi".to_string(),
            "rsi".to_string(),
            "rdx".to_string(),
            "rcx".to_string(),
            "r8".to_string(),
            "r9".to_string(),
        ]));
        let env = PassEnv {
            ptr_size: 8,
            sp_name: "rsp",
            fp_name: "rbp",
            ret_reg_name: "rax",
            function_names: empty_u64,
            strings: empty_u64,
            symbols: empty_u64,
            callee_resolution: None,
            arg_regs,
            param_register_aliases: empty_str,
            caller_saved_regs: empty_saved,
            type_hints: empty_ty,
            type_oracle: None,
        };

        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        let mut info = analysis::UseInfo::analyze(&fold_blocks, &env);
        analysis::use_info::annotate_stack_slot_semantics(
            &mut info,
            &func,
            &HashSet::from([-4]),
            &env,
        );

        assert!(info.stack_slots.values().any(|slot| {
            slot.offset == -4
                && slot.return_carrier
                && slot.value_kind == crate::analysis::StackSlotValueKind::Scalar
        }));
    }

    #[test]
    fn test_arm64_return_slot_merge_blocks_fold_to_concrete_returns() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: Varnode::constant(0x1008, 8),
                    cond: Varnode::constant(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: Varnode::constant(0x100c, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: Varnode::constant(0x100c, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa func");
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntSub {
                dst: make_var("SP", 1, 8),
                a: make_var("SP", 0, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntNotEqual {
                dst: make_var("tmp:cond", 1, 1),
                a: make_var("X0", 0, 8),
                b: make_var("const:dead", 0, 8),
            },
            SSAOp::CBranch {
                cond: make_var("tmp:cond", 1, 1),
                target: make_var("ram:1008", 0, 8),
            },
        ];
        func.get_block_mut(0x1004).expect("fallthrough").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:retaddr", 1, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:retaddr", 1, 8),
                val: make_var("const:1", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x1008).expect("taken").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:retaddr", 2, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:retaddr", 2, 8),
                val: make_var("const:0", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x100c).expect("exit").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:retaddr", 3, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:ret", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:retaddr", 3, 8),
            },
            SSAOp::IntZExt {
                dst: make_var("X0", 1, 8),
                src: make_var("tmp:ret", 1, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:sp", 1, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("SP", 2, 8),
                src: make_var("tmp:sp", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("PC", 1, 8),
                src: make_var("X30", 0, 8),
            },
            SSAOp::Return {
                target: make_var("PC", 1, 8),
            },
        ];

        let mut ctx = make_aarch64_ctx();
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        ctx.analyze_blocks(&fold_blocks);
        ctx.analyze_function_structure(&func);

        assert!(ctx.state.return_blocks.contains(&0x1004));
        assert!(ctx.state.return_blocks.contains(&0x1008));
        assert!(ctx.state.return_stack_slots.contains(&12));

        let then_stmts = ctx.fold_block(func.get_block(0x1008).expect("then"), 0x1008);
        let else_stmts = ctx.fold_block(func.get_block(0x1004).expect("else"), 0x1004);

        let Some(CStmt::Return(Some(then_expr))) = then_stmts.last() else {
            panic!("then block should fold to return");
        };
        let Some(CStmt::Return(Some(else_expr))) = else_stmts.last() else {
            panic!("else block should fold to return");
        };
        assert_eq!(then_expr, &CExpr::IntLit(0));
        assert_eq!(else_expr, &CExpr::IntLit(1));
    }

    #[test]
    fn test_x86_64_pure_control_exit_return_slot_merge_blocks_fold_to_concrete_returns() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: Varnode::constant(0x1008, 8),
                    cond: Varnode::constant(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: Varnode::constant(0x100c, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: Varnode::constant(0x100c, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa func");
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntSub {
                dst: make_var("RSP", 1, 8),
                a: make_var("RSP", 0, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::IntNotEqual {
                dst: make_var("tmp:cond", 1, 1),
                a: make_var("EDI", 0, 4),
                b: make_var("const:64", 0, 4),
            },
            SSAOp::CBranch {
                cond: make_var("tmp:cond", 1, 1),
                target: make_var("ram:1008", 0, 8),
            },
        ];
        func.get_block_mut(0x1004).expect("fallthrough").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:retaddr", 1, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:retaddr", 1, 8),
                val: make_var("const:1", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x1008).expect("taken").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:retaddr", 2, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:retaddr", 2, 8),
                val: make_var("const:0", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x100c).expect("exit").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:retaddr", 3, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:ret", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:retaddr", 3, 8),
            },
            SSAOp::IntZExt {
                dst: make_var("RAX", 1, 8),
                src: make_var("tmp:ret", 1, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("RSP", 2, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("RIP", 1, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 2, 8),
            },
            SSAOp::Return {
                target: make_var("RIP", 1, 8),
            },
        ];

        let mut ctx = make_x86_64_ctx();
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        ctx.analyze_blocks(&fold_blocks);
        ctx.analyze_function_structure(&func);

        assert!(ctx.state.return_blocks.contains(&0x1004));
        assert!(ctx.state.return_blocks.contains(&0x1008));
        assert!(ctx.state.return_stack_slots.contains(&-4));

        let then_stmts = ctx.fold_block(func.get_block(0x1008).expect("then"), 0x1008);
        let else_stmts = ctx.fold_block(func.get_block(0x1004).expect("else"), 0x1004);

        let Some(CStmt::Return(Some(then_expr))) = then_stmts.last() else {
            panic!("then block should fold to return, got {then_stmts:?}");
        };
        let Some(CStmt::Return(Some(else_expr))) = else_stmts.last() else {
            panic!("else block should fold to return, got {else_stmts:?}");
        };
        assert_eq!(then_expr, &CExpr::IntLit(0));
        assert_eq!(else_expr, &CExpr::IntLit(1));
    }

    #[test]
    fn conditional_loop_latch_with_exit_edge_is_not_whole_return_context() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: Varnode::constant(0x1004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: Varnode::constant(0x1000, 8),
                    cond: Varnode::constant(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa func");
        func.get_block_mut(0x1000).expect("header").ops = vec![SSAOp::Branch {
            target: make_var("ram:1004", 0, 8),
        }];
        func.get_block_mut(0x1004).expect("latch").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("RAX", 1, 8),
                a: make_var("RAX", 0, 8),
                b: make_var("const:1", 0, 8),
            },
            SSAOp::IntNotEqual {
                dst: make_var("tmp:cond", 1, 1),
                a: make_var("RSI", 0, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::CBranch {
                target: make_var("ram:1000", 0, 8),
                cond: make_var("tmp:cond", 1, 1),
            },
        ];
        func.get_block_mut(0x1008).expect("exit").ops = vec![SSAOp::Return {
            target: make_var("RIP", 1, 8),
        }];

        let mut ctx = make_x86_64_ctx();
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        ctx.analyze_blocks(&fold_blocks);
        ctx.analyze_function_structure(&func);

        assert!(
            !ctx.state.return_blocks.contains(&0x1004),
            "loop latch has a return edge, not block-wide return semantics: {:?}",
            ctx.state.return_blocks
        );

        let latch_stmts = ctx.fold_block(func.get_block(0x1004).expect("latch"), 0x1004);
        assert!(
            !latch_stmts
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(_))),
            "loop latch must not synthesize an unconditional return: {latch_stmts:?}"
        );
    }

    #[test]
    fn conditional_preheader_with_exit_edge_and_body_successor_is_not_whole_return_context() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: Varnode::constant(0x1008, 8),
                    cond: Varnode::constant(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: Varnode::constant(0x1004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa func");
        func.get_block_mut(0x1000).expect("preheader").ops = vec![
            SSAOp::Copy {
                dst: make_var("RAX", 1, 8),
                src: make_var("const:14650fb0739d0383", 0, 8),
            },
            SSAOp::IntNotEqual {
                dst: make_var("tmp:cond", 1, 1),
                a: make_var("RSI", 0, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::CBranch {
                target: make_var("ram:1008", 0, 8),
                cond: make_var("tmp:cond", 1, 1),
            },
        ];
        func.get_block_mut(0x1004).expect("body").ops = vec![SSAOp::Branch {
            target: make_var("ram:1004", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("exit").ops = vec![SSAOp::Return {
            target: make_var("RIP", 1, 8),
        }];

        let mut ctx = make_x86_64_ctx();
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        ctx.analyze_blocks(&fold_blocks);
        ctx.analyze_function_structure(&func);

        assert!(
            !ctx.state.return_blocks.contains(&0x1000),
            "preheader has both an exit edge and a body edge, not block-wide return semantics: {:?}",
            ctx.state.return_blocks
        );

        let preheader_stmts = ctx.fold_block(func.get_block(0x1000).expect("preheader"), 0x1000);
        assert!(
            !preheader_stmts
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(_))),
            "preheader must not synthesize an unconditional return: {preheader_stmts:?}"
        );
    }

    #[test]
    fn phi_sources_count_as_edge_uses_for_liveness() {
        use r2ssa::PhiNode;

        let rax_1 = make_var("RAX", 1, 8);
        let rax_2 = make_var("RAX", 2, 8);
        let blocks = vec![
            SSABlock {
                addr: 0x1000,
                size: 4,
                phis: Vec::new(),
                ops: vec![
                    SSAOp::IntAdd {
                        dst: rax_1.clone(),
                        a: make_var("RAX", 0, 8),
                        b: make_var("const:1", 0, 8),
                    },
                    SSAOp::Branch {
                        target: make_var("ram:1004", 0, 8),
                    },
                ],
            },
            SSABlock {
                addr: 0x1004,
                size: 4,
                phis: vec![PhiNode {
                    dst: rax_2.clone(),
                    sources: vec![(0x1000, rax_1.clone())],
                }],
                ops: vec![SSAOp::Return { target: rax_2 }],
            },
        ];

        let mut ctx = make_x86_64_ctx();
        ctx.analyze_blocks(&blocks);

        assert_eq!(
            ctx.use_counts_map().get("RAX_1").copied(),
            Some(1),
            "phi operands are edge uses and must keep loop-carried values live"
        );
        assert!(
            !ctx.is_dead(&rax_1),
            "phi source should not be pruned as a dead caller-saved register"
        );
    }

    #[test]
    fn loop_carried_phi_members_are_materialized_not_inlined() {
        use r2ssa::PhiNode;

        let rax_1 = make_var("RAX", 1, 8);
        let rax_2 = make_var("RAX", 2, 8);
        let rax_3 = make_var("RAX", 3, 8);
        let blocks = vec![
            SSABlock {
                addr: 0x1000,
                size: 4,
                phis: Vec::new(),
                ops: vec![
                    SSAOp::Copy {
                        dst: rax_1.clone(),
                        src: make_var("const:14650fb0739d0383", 0, 8),
                    },
                    SSAOp::Branch {
                        target: make_var("ram:1010", 0, 8),
                    },
                ],
            },
            SSABlock {
                addr: 0x1010,
                size: 4,
                phis: vec![PhiNode {
                    dst: rax_2.clone(),
                    sources: vec![(0x1000, rax_1.clone()), (0x1020, rax_3.clone())],
                }],
                ops: vec![SSAOp::CBranch {
                    target: make_var("ram:1020", 0, 8),
                    cond: make_var("const:1", 0, 1),
                }],
            },
            SSABlock {
                addr: 0x1020,
                size: 4,
                phis: Vec::new(),
                ops: vec![
                    SSAOp::IntAdd {
                        dst: rax_3.clone(),
                        a: rax_2.clone(),
                        b: make_var("const:1", 0, 8),
                    },
                    SSAOp::CBranch {
                        target: make_var("ram:1010", 0, 8),
                        cond: make_var("const:1", 0, 1),
                    },
                ],
            },
        ];

        let mut ctx = make_x86_64_ctx();
        ctx.analyze_blocks(&blocks);

        assert!(
            ctx.pinned_set().contains("RAX_1")
                && ctx.pinned_set().contains("RAX_2")
                && ctx.pinned_set().contains("RAX_3"),
            "loop-carried phi class should be pinned for out-of-SSA materialization: {:?}",
            ctx.pinned_set()
        );
        assert!(
            !ctx.is_dead(&rax_3),
            "pinned loop-carried update should not be considered dead; uses={:?} pinned={:?}",
            ctx.use_counts_map(),
            ctx.pinned_set()
        );
        assert!(
            !ctx.should_inline(&rax_3),
            "pinned loop-carried update should not be inlined"
        );
        assert!(
            !ctx.should_suppress_shadow_call_result_assignment(&rax_3),
            "loop-carried update should not be suppressed as a call-result shadow"
        );
        let direct_stmt = ctx.op_to_stmt_with_args(&blocks[2].ops[0], 0x1020, 0);
        assert!(
            direct_stmt.is_some(),
            "loop-carried update should lower to a statement before block pruning"
        );

        let latch_stmts = ctx.fold_block(blocks.get(2).expect("latch"), 0x1020);
        assert!(
            latch_stmts.iter().any(|stmt| {
                matches!(
                    stmt,
                    CStmt::Expr(CExpr::Binary {
                        op: BinaryOp::Assign,
                        ..
                    })
                )
            }),
            "loop-carried recurrence update must survive as a materialized assignment: {latch_stmts:?}"
        );
    }

    #[test]
    fn test_x86_64_saved_fp_reload_epilogue_still_marks_branch_arms_as_return_blocks() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: Varnode::constant(0x1008, 8),
                    cond: Varnode::constant(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: Varnode::constant(0x100c, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: Varnode::constant(0x100c, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa func");
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntSub {
                dst: make_var("RSP", 1, 8),
                a: make_var("RSP", 0, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::IntNotEqual {
                dst: make_var("tmp:cond", 1, 1),
                a: make_var("EDI", 0, 4),
                b: make_var("const:dead", 0, 4),
            },
            SSAOp::CBranch {
                cond: make_var("tmp:cond", 1, 1),
                target: make_var("ram:1008", 0, 8),
            },
        ];
        func.get_block_mut(0x1004).expect("then").ops = vec![
            SSAOp::Copy {
                dst: make_var("RAX", 1, 8),
                src: make_var("const:1", 0, 8),
            },
            SSAOp::Branch {
                target: make_var("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x1008).expect("else").ops = vec![SSAOp::Copy {
            dst: make_var("RAX", 2, 8),
            src: make_var("const:0", 0, 8),
        }];
        func.get_block_mut(0x100c).expect("exit").ops = vec![
            SSAOp::Load {
                dst: make_var("tmp:savedfp", 1, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 1, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("RSP", 2, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("RBP", 1, 8),
                src: make_var("tmp:savedfp", 1, 8),
            },
            SSAOp::Load {
                dst: make_var("RIP", 1, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 2, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("RSP", 3, 8),
                a: make_var("RSP", 2, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Return {
                target: make_var("RIP", 1, 8),
            },
        ];

        let mut ctx = make_x86_64_ctx();
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        ctx.analyze_blocks(&fold_blocks);
        ctx.analyze_function_structure(&func);

        assert!(
            ctx.state.return_blocks.contains(&0x1004),
            "then arm should be a return block, got {:?}",
            ctx.state.return_blocks
        );
        assert!(
            ctx.state.return_blocks.contains(&0x1008),
            "else arm should be a return block, got {:?}",
            ctx.state.return_blocks
        );

        let then_stmts = ctx.fold_block(func.get_block(0x1004).expect("then"), 0x1004);
        let else_stmts = ctx.fold_block(func.get_block(0x1008).expect("else"), 0x1008);

        let Some(CStmt::Return(Some(then_expr))) = then_stmts.last() else {
            panic!("then block should fold to return, got {then_stmts:?}");
        };
        let Some(CStmt::Return(Some(else_expr))) = else_stmts.last() else {
            panic!("else block should fold to return, got {else_stmts:?}");
        };
        assert_eq!(then_expr, &CExpr::IntLit(1));
        assert_eq!(else_expr, &CExpr::IntLit(0));
    }

    #[test]
    fn decompile_x86_check_secret_like_cfg_with_saved_fp_epilogue_keeps_branch_returns() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: Varnode::constant(0x1008, 8),
                    cond: Varnode::constant(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: Varnode::constant(0x100c, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa func");
        func = func.with_name("sym._check_secret_like");
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntSub {
                dst: make_var("RSP", 1, 8),
                a: make_var("RSP", 0, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 1, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:6a80", 1, 4),
                src: make_var("EDI", 0, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 1, 8),
                val: make_var("tmp:6a80", 1, 4),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 1, 8),
            },
            SSAOp::IntSub {
                dst: make_var("tmp:3e580", 1, 4),
                a: make_var("tmp:11f00", 1, 4),
                b: make_var("const:dead", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("ZF", 1, 1),
                a: make_var("tmp:3e580", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:12800", 1, 1),
                src: make_var("ZF", 1, 1),
            },
            SSAOp::CBranch {
                cond: make_var("tmp:12800", 1, 1),
                target: make_var("ram:1008", 0, 8),
            },
        ];
        func.get_block_mut(0x1004).expect("then").ops = vec![
            SSAOp::Copy {
                dst: make_var("RAX", 1, 8),
                src: make_var("const:1", 0, 8),
            },
            SSAOp::Branch {
                target: make_var("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x1008).expect("else").ops = vec![SSAOp::Copy {
            dst: make_var("RAX", 2, 8),
            src: make_var("const:0", 0, 8),
        }];
        func.get_block_mut(0x100c).expect("exit").ops = vec![
            SSAOp::Load {
                dst: make_var("tmp:savedfp", 1, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 1, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("RSP", 2, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("RBP", 1, 8),
                src: make_var("tmp:savedfp", 1, 8),
            },
            SSAOp::Load {
                dst: make_var("RIP", 1, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 2, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("RSP", 3, 8),
                a: make_var("RSP", 2, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Return {
                target: make_var("RIP", 1, 8),
            },
        ];

        let decompiler = crate::Decompiler::new(crate::DecompilerConfig::x86_64());
        let output = decompiler.decompile(&func);
        assert!(
            output.contains("if") && output.contains("return 1;") && output.contains("return 0;"),
            "expected source-like branch returns, got:\n{output}"
        );
    }

    #[test]
    fn decompile_x86_check_secret_observed_shape_keeps_branch_returns() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x401276,
                size: 20,
                ops: vec![R2ILOp::CBranch {
                    target: Varnode::constant(0x401291, 8),
                    cond: Varnode::constant(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x40128a,
                size: 7,
                ops: vec![R2ILOp::Branch {
                    target: Varnode::constant(0x401296, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x401291,
                size: 5,
                ops: vec![],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x401296,
                size: 2,
                ops: vec![R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa func");
        func = func.with_name("sym._check_secret_observed");
        func.get_block_mut(0x401276).expect("entry").ops = vec![
            SSAOp::Copy {
                dst: make_var("tmp:27d00", 1, 8),
                src: make_var("RBP", 0, 8),
            },
            SSAOp::IntSub {
                dst: make_var("RSP", 1, 8),
                a: make_var("RSP", 0, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("RSP", 1, 8),
                val: make_var("tmp:27d00", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("RBP", 1, 8),
                src: make_var("RSP", 1, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 1, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:6a80", 1, 4),
                src: make_var("EDI", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 1, 8),
                val: make_var("tmp:6a80", 1, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 2, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 2, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:3e480", 1, 4),
                src: make_var("tmp:11f00", 1, 4),
            },
            SSAOp::IntLess {
                dst: make_var("CF", 1, 1),
                a: make_var("tmp:3e480", 1, 4),
                b: make_var("const:dead", 0, 4),
            },
            SSAOp::IntSBorrow {
                dst: make_var("OF", 1, 1),
                a: make_var("tmp:3e480", 1, 4),
                b: make_var("const:dead", 0, 4),
            },
            SSAOp::IntSub {
                dst: make_var("tmp:3e580", 1, 4),
                a: make_var("tmp:3e480", 1, 4),
                b: make_var("const:dead", 0, 4),
            },
            SSAOp::IntSLess {
                dst: make_var("SF", 1, 1),
                a: make_var("tmp:3e580", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("ZF", 1, 1),
                a: make_var("tmp:3e580", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c200", 1, 4),
                a: make_var("tmp:3e580", 1, 4),
                b: make_var("const:ff", 0, 4),
            },
            SSAOp::PopCount {
                dst: make_var("tmp:2c280", 1, 1),
                src: make_var("tmp:2c200", 1, 4),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c300", 1, 1),
                a: make_var("tmp:2c280", 1, 1),
                b: make_var("const:1", 0, 1),
            },
            SSAOp::IntEqual {
                dst: make_var("PF", 1, 1),
                a: make_var("tmp:2c300", 1, 1),
                b: make_var("const:0", 0, 1),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:12800", 1, 1),
                src: make_var("ZF", 1, 1),
            },
            SSAOp::CBranch {
                cond: make_var("tmp:12800", 1, 1),
                target: make_var("ram:401291", 0, 8),
            },
        ];
        func.get_block_mut(0x40128a).expect("then").ops = vec![
            SSAOp::Copy {
                dst: make_var("RAX", 1, 8),
                src: make_var("const:1", 0, 8),
            },
            SSAOp::Branch {
                target: make_var("ram:401296", 0, 8),
            },
        ];
        func.get_block_mut(0x401291).expect("else").ops = vec![SSAOp::Copy {
            dst: make_var("RAX", 2, 8),
            src: make_var("const:0", 0, 8),
        }];
        func.get_block_mut(0x401296).expect("exit").ops = vec![
            SSAOp::Copy {
                dst: make_var("tmp:55400", 1, 8),
                src: make_var("const:0", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:55400", 2, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 1, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("RSP", 2, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("RBP", 2, 8),
                src: make_var("tmp:55400", 2, 8),
            },
            SSAOp::Load {
                dst: make_var("RIP", 1, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 2, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("RSP", 3, 8),
                a: make_var("RSP", 2, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Return {
                target: make_var("RIP", 1, 8),
            },
        ];

        let mut ctx = make_x86_64_ctx();
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        ctx.analyze_blocks(&fold_blocks);
        ctx.analyze_function_structure(&func);
        assert!(
            ctx.state.return_blocks.contains(&0x40128a),
            "then arm should be a return block, got {:?}",
            ctx.state.return_blocks
        );
        assert!(
            ctx.state.return_blocks.contains(&0x401291),
            "else arm should be a return block, got {:?}",
            ctx.state.return_blocks
        );
        let cond = ctx
            .extract_condition_from_block(func.get_block(0x401276).expect("entry"))
            .expect("structured condition");
        assert!(
            matches!(cond, CExpr::Binary { .. }),
            "expected a structured condition, got {cond:?}"
        );

        let decompiler = crate::Decompiler::new(crate::DecompilerConfig::x86_64());
        let output = decompiler.decompile(&func);
        assert!(
            output.contains("if") && output.contains("return 1;") && output.contains("return 0;"),
            "expected observed x86 check_secret shape to keep branch returns, got:\n{output}"
        );
    }

    #[test]
    fn test_return_expr_inlines_simple_xor_chain_and_stops_after_return() {
        let eax_1 = make_var("EAX", 1, 4);
        let edi_0 = make_var("EDI", 0, 4);
        let esi_0 = make_var("ESI", 0, 4);
        let t1 = make_var("tmp:8000", 1, 1);
        let t2 = make_var("tmp:8001", 1, 1);
        let t3 = make_var("tmp:8002", 1, 1);
        let rip_1 = make_var("RIP", 1, 8);
        let const_0 = make_var("const:0", 0, 4);

        let block = make_block(vec![
            SSAOp::IntNotEqual {
                dst: t1.clone(),
                a: edi_0,
                b: const_0.clone(),
            },
            SSAOp::IntNotEqual {
                dst: t2.clone(),
                a: esi_0,
                b: const_0,
            },
            SSAOp::IntXor {
                dst: t3.clone(),
                a: t1,
                b: t2,
            },
            SSAOp::Copy {
                dst: eax_1,
                src: t3,
            },
            SSAOp::Return { target: rip_1 },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);
        ctx.state.return_blocks.insert(block.addr);

        let stmts = ctx.fold_block(&block, block.addr);
        assert_eq!(
            stmts.len(),
            1,
            "Should stop emitting after high-level return"
        );

        match &stmts[0] {
            CStmt::Return(Some(expr)) => {
                assert!(
                    expr_contains_binary_op(expr, BinaryOp::BitXor),
                    "Return expression should inline XOR chain"
                );
                assert!(
                    expr_contains_binary_op(expr, BinaryOp::Ne),
                    "Return expression should include inlined predicate comparisons"
                );
            }
            other => panic!("Expected return statement, got {:?}", other),
        }
    }

    #[test]
    fn test_signed_idiv_return_uses_low_signed_dividend_root() {
        let ecx_1 = make_var("ECX", 1, 4);
        let eax_1 = make_var("EAX", 1, 4);
        let edx_1 = make_var("EDX", 1, 4);
        let sext_eax = make_var("tmp:3d680", 1, 8);
        let sext_ecx = make_var("tmp:49680", 1, 8);
        let high_zext = make_var("tmp:49700", 1, 8);
        let shifted_high = make_var("tmp:49780", 1, 8);
        let low_zext = make_var("tmp:49800", 1, 8);
        let dividend = make_var("tmp:49900", 1, 8);
        let quotient = make_var("tmp:49a00", 1, 8);
        let eax_2 = make_var("EAX", 2, 4);
        let rip_1 = make_var("RIP", 1, 8);

        let block = make_block(vec![
            SSAOp::Copy {
                dst: ecx_1.clone(),
                src: make_var("EDX", 0, 4),
            },
            SSAOp::Copy {
                dst: eax_1.clone(),
                src: make_var("ESI", 0, 4),
            },
            SSAOp::IntSExt {
                dst: sext_eax.clone(),
                src: eax_1.clone(),
            },
            SSAOp::Subpiece {
                dst: edx_1.clone(),
                src: sext_eax,
                offset: 4,
            },
            SSAOp::IntZExt {
                dst: high_zext.clone(),
                src: edx_1,
            },
            SSAOp::IntLeft {
                dst: shifted_high.clone(),
                a: high_zext,
                b: make_var("const:20", 0, 8),
            },
            SSAOp::IntZExt {
                dst: low_zext.clone(),
                src: eax_1.clone(),
            },
            SSAOp::IntOr {
                dst: dividend.clone(),
                a: shifted_high,
                b: low_zext,
            },
            SSAOp::IntSExt {
                dst: sext_ecx.clone(),
                src: ecx_1,
            },
            SSAOp::IntSDiv {
                dst: quotient.clone(),
                a: dividend.clone(),
                b: sext_ecx,
            },
            SSAOp::Subpiece {
                dst: eax_2,
                src: quotient,
                offset: 0,
            },
            SSAOp::Return { target: rip_1 },
        ]);

        let mut ctx = make_x86_64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([
            ("esi".to_string(), "a".to_string()),
            ("edx".to_string(), "b".to_string()),
        ])));
        ctx.analyze_block(&block);
        ctx.state.return_blocks.insert(block.addr);
        assert_eq!(
            ctx.signed_extended_dividend_low_root(&dividend),
            Some(eax_1),
            "signed idiv producer proof should recover the low dividend root"
        );

        let stmts = ctx.fold_block(&block, block.addr);
        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("expected signed division return, got {stmts:?}");
        };
        assert_eq!(
            expr,
            &CExpr::binary(
                BinaryOp::Div,
                CExpr::Var("a".to_string()),
                CExpr::Var("b".to_string())
            )
        );
        assert!(
            stmts.iter().all(|stmt| {
                let rendered = format!("{stmt:?}");
                !rendered.contains("t49900") && !rendered.contains("t49a00")
            }),
            "signed idiv lowering should not leak dividend construction temps: {stmts:?}"
        );
    }

    #[test]
    fn test_signed_idiv_accepts_direct_sign_extended_high_limb() {
        let ecx_1 = make_var("ECX", 1, 4);
        let eax_1 = make_var("EAX", 1, 4);
        let sext_eax = make_var("tmp:3d680", 1, 8);
        let sext_ecx = make_var("tmp:49680", 1, 8);
        let high_zext = make_var("tmp:49700", 1, 8);
        let shifted_high = make_var("tmp:49780", 1, 8);
        let low_zext = make_var("tmp:49800", 1, 8);
        let dividend = make_var("tmp:49900", 1, 8);
        let quotient = make_var("tmp:49a00", 1, 8);
        let eax_2 = make_var("EAX", 2, 4);
        let rip_1 = make_var("RIP", 1, 8);

        let block = make_block(vec![
            SSAOp::Copy {
                dst: ecx_1.clone(),
                src: make_var("EDX", 0, 4),
            },
            SSAOp::Copy {
                dst: eax_1.clone(),
                src: make_var("ESI", 0, 4),
            },
            SSAOp::IntSExt {
                dst: sext_eax.clone(),
                src: eax_1.clone(),
            },
            SSAOp::IntZExt {
                dst: high_zext.clone(),
                src: sext_eax,
            },
            SSAOp::IntLeft {
                dst: shifted_high.clone(),
                a: high_zext,
                b: make_var("const:20", 0, 8),
            },
            SSAOp::IntZExt {
                dst: low_zext.clone(),
                src: eax_1.clone(),
            },
            SSAOp::IntOr {
                dst: dividend.clone(),
                a: shifted_high,
                b: low_zext,
            },
            SSAOp::IntSExt {
                dst: sext_ecx.clone(),
                src: ecx_1,
            },
            SSAOp::IntSDiv {
                dst: quotient.clone(),
                a: dividend.clone(),
                b: sext_ecx,
            },
            SSAOp::Subpiece {
                dst: eax_2,
                src: quotient,
                offset: 0,
            },
            SSAOp::Return { target: rip_1 },
        ]);

        let mut ctx = make_x86_64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([
            ("esi".to_string(), "a".to_string()),
            ("edx".to_string(), "b".to_string()),
        ])));
        ctx.analyze_block(&block);
        ctx.state.return_blocks.insert(block.addr);

        let stmts = ctx.fold_block(&block, block.addr);
        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("expected signed division return, got {stmts:?}");
        };
        assert_eq!(
            expr,
            &CExpr::binary(
                BinaryOp::Div,
                CExpr::Var("a".to_string()),
                CExpr::Var("b".to_string())
            )
        );
    }

    #[test]
    fn test_no_duplicate_low_level_return_after_high_level_return() {
        let eax_1 = make_var("EAX", 1, 4);
        let tmp = make_var("tmp:8100", 1, 4);
        let rip_1 = make_var("RIP", 1, 8);

        let block = make_block(vec![
            SSAOp::Copy {
                dst: tmp.clone(),
                src: make_var("const:1", 0, 4),
            },
            SSAOp::Copy {
                dst: eax_1,
                src: tmp,
            },
            SSAOp::Return { target: rip_1 },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);
        ctx.state.return_blocks.insert(block.addr);

        let stmts = ctx.fold_block(&block, block.addr);
        let return_count = stmts
            .iter()
            .filter(|stmt| matches!(stmt, CStmt::Return(_)))
            .count();
        assert_eq!(return_count, 1, "Should emit a single high-level return");
    }

    #[test]
    fn test_non_return_block_return_rax0_uses_last_return_value() {
        let rax_1 = make_var("RAX", 1, 8);
        let rax_0 = make_var("RAX", 0, 8);

        let block = make_block(vec![
            SSAOp::Copy {
                dst: rax_1.clone(),
                src: make_var("const:2a", 0, 8),
            },
            SSAOp::Copy {
                dst: rax_0.clone(),
                src: rax_1,
            },
            SSAOp::Return { target: rax_0 },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);
        let stmts = ctx.fold_block(&block, block.addr);

        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("Expected trailing return statement");
        };
        assert!(
            !matches!(expr, CExpr::Var(name) if name.eq_ignore_ascii_case("rax_0")),
            "Return should not keep unresolved RAX_0 artifact in non-return blocks"
        );
    }

    #[test]
    fn test_non_return_block_return_eax0_uses_last_return_value() {
        let eax_1 = make_var("EAX", 1, 4);
        let eax_0 = make_var("EAX", 0, 4);

        let block = make_block(vec![
            SSAOp::Copy {
                dst: eax_1.clone(),
                src: make_var("const:7", 0, 4),
            },
            SSAOp::Copy {
                dst: eax_0.clone(),
                src: eax_1,
            },
            SSAOp::Return { target: eax_0 },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);
        let stmts = ctx.fold_block(&block, block.addr);

        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("Expected trailing return statement");
        };
        assert!(
            !matches!(expr, CExpr::Var(name) if name.eq_ignore_ascii_case("eax_0")),
            "Return should not keep unresolved EAX_0 artifact in non-return blocks"
        );
    }

    #[test]
    fn test_non_return_block_return_rax0_kept_when_no_resolution_available() {
        let block = make_block(vec![SSAOp::Return {
            target: make_var("RAX", 0, 8),
        }]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);
        let stmts = ctx.fold_block(&block, block.addr);

        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("Expected trailing return statement");
        };
        assert!(
            matches!(expr, CExpr::Var(name) if name.eq_ignore_ascii_case("rax_0") || name.eq_ignore_ascii_case("rax")),
            "Return register should remain unresolved when no better return value can be derived"
        );
    }

    #[test]
    fn test_return_does_not_collapse_to_generic_stack_alias() {
        let ret = make_var("tmp:ret", 1, 8);
        let block = make_block(vec![SSAOp::Return {
            target: ret.clone(),
        }]);

        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.use_info.definitions.insert(
            ret.display_name(),
            CExpr::Deref(Box::new(CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("rbp".to_string()),
                CExpr::IntLit(0),
            ))),
        );
        ctx.analyze_block(&block);
        let stmts = ctx.fold_block(&block, block.addr);

        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("Expected trailing return statement");
        };
        assert!(
            !matches!(expr, CExpr::Var(name) if name == "stack_0" || name == "saved_fp"),
            "Generic stack placeholders must not leak into visible return expressions"
        );
    }

    #[test]
    fn test_return_does_not_collapse_to_plain_stack_alias() {
        let ret = make_var("tmp:ret2", 1, 8);
        let block = make_block(vec![SSAOp::Return {
            target: ret.clone(),
        }]);

        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert(ret.display_name(), CExpr::Var("stack".to_string()));
        ctx.analyze_block(&block);
        let stmts = ctx.fold_block(&block, block.addr);

        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("Expected trailing return statement");
        };
        assert!(
            !matches!(expr, CExpr::Var(name) if name == "stack"),
            "plain stack placeholder must not survive in final return expressions"
        );
    }

    #[test]
    fn test_return_prefers_semantic_value_over_unresolved_return_register() {
        let ret = make_var("RAX", 0, 8);
        let block = make_block(vec![SSAOp::Return {
            target: ret.clone(),
        }]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert(ret.display_name(), CExpr::Var("rax_0".to_string()));
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("resolved_1".to_string(), CExpr::Var("arg1".to_string()));
        ctx.state.analysis_ctx.use_info.forwarded_values.insert(
            ret.display_name(),
            crate::analysis::ValueProvenance {
                source: "resolved_1".to_string(),
                source_value_id: None,
                source_var: None,
                stack_slot: None,
            },
        );
        let stmts = ctx.fold_block(&block, block.addr);

        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("Expected trailing return statement");
        };
        assert_eq!(
            expr,
            &CExpr::Var("arg1".to_string()),
            "return selection should prefer the semantic forwarded value over the unresolved return register"
        );
    }

    #[test]
    fn test_return_control_artifact_prefers_last_semantic_return_value() {
        let rax_1 = make_var("RAX", 1, 8);
        let rip_1 = make_var("RIP", 1, 8);
        let block = make_block(vec![
            SSAOp::Copy {
                dst: rax_1.clone(),
                src: make_var("const:7", 0, 8),
            },
            SSAOp::Return { target: rip_1 },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);
        let stmts = ctx.fold_block(&block, block.addr);

        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("Expected trailing return statement");
        };
        assert_eq!(
            expr,
            &CExpr::IntLit(7),
            "control-artifact return targets should defer to the tracked semantic return value"
        );
    }

    #[test]
    fn test_control_epilogue_load_does_not_mask_merged_return_register_phi() {
        use r2il::{R2ILBlock, R2ILOp, RegisterDef, Varnode};

        let mut arch = make_test_arch_x86_64();
        arch.add_register(RegisterDef::new("RIP", 0x30, 8));
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1008, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut left = R2ILBlock::new(0x1004, 4);
        left.push(R2ILOp::Copy {
            dst: Varnode::register(0x00, 8),
            src: Varnode::constant(1, 8),
        });
        left.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });
        let mut right = R2ILBlock::new(0x1008, 4);
        right.push(R2ILOp::Copy {
            dst: Varnode::register(0x00, 8),
            src: Varnode::constant(1, 8),
        });
        right.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });
        let mut exit = R2ILBlock::new(0x100c, 4);
        exit.push(R2ILOp::Load {
            dst: Varnode::register(0x30, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(0x28, 8),
        });
        exit.push(R2ILOp::Return {
            target: Varnode::register(0x30, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry, left, right, exit], &arch);
        let func = prepared.function();
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.analyze_blocks(&func.blocks().cloned().collect::<Vec<_>>());
        ctx.analyze_function_structure(func);

        let exit_block = func.get_block(0x100c).expect("exit block");
        let stmts = ctx.fold_block(exit_block, exit_block.addr);
        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("expected trailing return statement, got {stmts:?}");
        };
        assert_eq!(
            expr,
            &CExpr::IntLit(1),
            "control epilogue load should not mask merged return-register phi"
        );
    }

    #[test]
    fn test_return_register_write_keeps_semantic_indexed_load_shape() {
        let idx_src = make_var("ESI", 0, 4);
        let arr_src = make_var("RDI", 0, 8);
        let eax = make_var("EAX", 2, 4);
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .type_hints
            .insert(arr_src.display_name(), CType::ptr(CType::Int(32)));
        ctx.state
            .analysis_ctx
            .use_info
            .type_hints
            .insert(idx_src.display_name(), CType::Int(32));
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            eax.display_name(),
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(arr_src)),
                    index: Some(crate::analysis::ValueRef::from(idx_src)),
                    scale_bytes: 4,
                    offset_bytes: 0,
                },
                size: 4,
            },
        );
        assert!(
            ctx.lookup_semantic_value(&eax.display_name()).is_some(),
            "semantic value should be present for the return source"
        );
        let mut base_visited = HashSet::new();
        let base_rendered = ctx.render_value_ref(
            &crate::analysis::ValueRef::from(make_var("RDI", 0, 8)),
            0,
            &mut base_visited,
        );
        let mut index_visited = HashSet::new();
        let index_rendered = ctx.render_value_ref(
            &crate::analysis::ValueRef::from(make_var("ESI", 0, 4)),
            0,
            &mut index_visited,
        );
        assert!(base_rendered.is_some(), "base should render");
        assert!(index_rendered.is_some(), "index should render");
        let mut visited = HashSet::new();
        let semantic = ctx.render_semantic_value_by_name(&eax.display_name(), 0, &mut visited);
        assert!(
            matches!(semantic, Some(CExpr::Subscript { .. })),
            "semantic return source should render as subscript before return selection, got {semantic:?}"
        );
        let expr = ctx.get_return_expr(&eax);
        assert!(
            matches!(expr, CExpr::Subscript { .. }),
            "semantic indexed load should survive get_return_expr for return-register sources, got {expr:?}"
        );
    }

    #[test]
    fn test_observed_x86_positive_index_folded_return_promotes_to_subscript() {
        let rbp = make_var("RBP", 0, 8);
        let rdi = make_var("RDI", 0, 8);
        let esi = make_var("ESI", 0, 4);
        let slot_arr = make_var("tmp:4700", 1, 8);
        let slot_idx = make_var("tmp:4700", 2, 8);
        let idx_loaded = make_var("tmp:11f00", 1, 4);
        let eax1 = make_var("EAX", 1, 4);
        let sext_idx = make_var("RAX", 2, 8);
        let scaled = make_var("tmp:4c80", 1, 8);
        let rdx1 = make_var("RDX", 1, 8);
        let arr_loaded = make_var("tmp:11f80", 1, 8);
        let rax3 = make_var("RAX", 3, 8);
        let addr = make_var("RAX", 4, 8);
        let load = make_var("tmp:11f00", 2, 4);
        let ret = make_var("EAX", 2, 4);
        let rip = make_var("RIP", 0, 8);

        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: slot_arr.clone(),
                a: rbp.clone(),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: slot_arr.clone(),
                val: rdi,
            },
            SSAOp::IntAdd {
                dst: slot_idx.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: slot_idx.clone(),
                val: esi,
            },
            SSAOp::Load {
                dst: idx_loaded.clone(),
                space: "ram".to_string(),
                addr: slot_idx,
            },
            SSAOp::Copy {
                dst: eax1.clone(),
                src: idx_loaded,
            },
            SSAOp::IntSExt {
                dst: sext_idx.clone(),
                src: eax1,
            },
            SSAOp::IntMult {
                dst: scaled.clone(),
                a: sext_idx,
                b: make_var("const:4", 0, 8),
            },
            SSAOp::Copy {
                dst: rdx1.clone(),
                src: scaled,
            },
            SSAOp::Load {
                dst: arr_loaded.clone(),
                space: "ram".to_string(),
                addr: slot_arr,
            },
            SSAOp::Copy {
                dst: rax3.clone(),
                src: arr_loaded,
            },
            SSAOp::IntAdd {
                dst: addr.clone(),
                a: rax3,
                b: rdx1,
            },
            SSAOp::Load {
                dst: load.clone(),
                space: "ram".to_string(),
                addr,
            },
            SSAOp::Copy {
                dst: ret.clone(),
                src: load,
            },
            SSAOp::Return { target: rip },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arr".to_string()),
                ("esi".to_string(), "idx".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                ("arr".to_string(), CType::ptr(CType::Int(32))),
                ("idx".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );

        ctx.analyze_blocks(std::slice::from_ref(&block));
        ctx.state.return_blocks.insert(block.addr);

        let stmts = ctx.fold_block(&block, block.addr);
        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("expected trailing return statement, got {stmts:?}");
        };
        let rendered = format!("{expr:?}");
        assert!(
            matches!(expr, CExpr::Subscript { .. }),
            "expected observed x86 positive-index return to render as subscript, got {expr:?}; stmts={stmts:?}"
        );
        assert!(
            rendered.contains("idx") || rendered.contains("arg2"),
            "expected observed x86 positive-index return to keep the semantic index, got {expr:?}"
        );
    }

    #[test]
    fn test_get_return_expr_keeps_both_semantic_member_loads_in_sum() {
        let base = make_var("RDI", 0, 8);
        let idx = make_var("ESI", 0, 4);
        let load_first = make_var("EAX", 1, 4);
        let load_second = make_var("tmp:11f00", 8, 4);
        let ret = make_var("EAX", 2, 4);
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                (
                    "arg1".to_string(),
                    CType::ptr(CType::Struct("DemoStruct".to_string())),
                ),
                ("arg2".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demostruct".to_string(),
                ExternalStruct {
                    name: "DemoStruct".to_string(),
                    fields: [
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
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            load_first.display_name(),
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(
                        base.clone(),
                    )),
                    index: Some(crate::analysis::ValueRef::from(idx.clone())),
                    scale_bytes: 0x38,
                    offset_bytes: 8,
                },
                size: 4,
            },
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            load_second.display_name(),
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(
                        base.clone(),
                    )),
                    index: Some(crate::analysis::ValueRef::from(idx.clone())),
                    scale_bytes: 0x38,
                    offset_bytes: 0x34,
                },
                size: 4,
            },
        );
        ctx.state.analysis_ctx.use_info.definitions.insert(
            ret.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var(load_first.display_name()),
                CExpr::Var(load_second.display_name()),
            ),
        );

        let expr = ctx.get_return_expr(&ret);
        let rendered = format!("{expr:?}");
        assert!(
            rendered.contains("third") && rendered.contains("fourteenth"),
            "expected both semantic member loads in return sum, got {expr:?}"
        );
        assert!(
            matches!(
                expr,
                CExpr::Binary {
                    op: BinaryOp::Add,
                    ..
                }
            ),
            "expected semantic return to stay a sum, got {expr:?}"
        );
    }

    #[test]
    fn test_fold_block_keeps_both_semantic_member_loads_in_return_sum() {
        let base = make_var("RDI", 0, 8);
        let idx = make_var("ESI", 0, 4);
        let load_first = make_var("EAX", 1, 4);
        let load_second = make_var("tmp:11f00", 8, 4);
        let ret = make_var("EAX", 2, 4);
        let rip = make_var("RIP", 0, 8);
        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: ret.clone(),
                a: load_first.clone(),
                b: load_second.clone(),
            },
            SSAOp::Return { target: rip },
        ]);

        let mut ctx = FoldingContext::new(64);
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                (
                    "arg1".to_string(),
                    CType::ptr(CType::Struct("DemoStruct".to_string())),
                ),
                ("arg2".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demostruct".to_string(),
                ExternalStruct {
                    name: "DemoStruct".to_string(),
                    fields: [
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
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));
        ctx.analyze_block(&block);
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            load_first.display_name(),
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(
                        base.clone(),
                    )),
                    index: Some(crate::analysis::ValueRef::from(idx.clone())),
                    scale_bytes: 0x38,
                    offset_bytes: 8,
                },
                size: 4,
            },
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            load_second.display_name(),
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(base)),
                    index: Some(crate::analysis::ValueRef::from(idx)),
                    scale_bytes: 0x38,
                    offset_bytes: 0x34,
                },
                size: 4,
            },
        );
        ctx.state.return_blocks.insert(block.addr);

        let stmts = ctx.fold_block(&block, block.addr);
        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("expected return statement, got {stmts:?}");
        };
        let rendered = format!("{expr:?}");
        assert!(
            rendered.contains("third") && rendered.contains("fourteenth"),
            "expected semantic member loads to survive tracked return emission, got {expr:?}"
        );
        assert!(
            matches!(
                expr,
                CExpr::Binary {
                    op: BinaryOp::Add,
                    ..
                }
            ),
            "expected return to stay a sum, got {expr:?}"
        );
        assert!(
            !rendered.contains("Deref") && !rendered.contains("IntLit(52)"),
            "raw pointer math should not survive tracked return emission, got {expr:?}"
        );
    }

    #[test]
    fn test_observed_x86_struct_array_loads_render_as_indexed_members_before_return_selection() {
        let block = make_block(vec![
            SSAOp::IntSub {
                dst: make_var("RSP", 1, 8),
                a: make_var("RSP", 0, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("RSP", 1, 8),
                val: make_var("RBP", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("RBP", 1, 8),
                src: make_var("RSP", 1, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 1, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 1, 8),
                val: make_var("RDI", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 2, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 2, 8),
                val: make_var("ESI", 0, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 3, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff0", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 3, 8),
                val: make_var("EDX", 0, 4),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 2, 8),
            },
            SSAOp::Copy {
                dst: make_var("EAX", 1, 4),
                src: make_var("tmp:11f00", 1, 4),
            },
            SSAOp::IntSExt {
                dst: make_var("RDX", 1, 8),
                src: make_var("EAX", 1, 4),
            },
            SSAOp::Copy {
                dst: make_var("RAX", 1, 8),
                src: make_var("RDX", 1, 8),
            },
            SSAOp::IntLeft {
                dst: make_var("RAX", 2, 8),
                a: make_var("RAX", 1, 8),
                b: make_var("const:3", 0, 8),
            },
            SSAOp::IntSub {
                dst: make_var("RAX", 3, 8),
                a: make_var("RAX", 2, 8),
                b: make_var("RDX", 1, 8),
            },
            SSAOp::IntLeft {
                dst: make_var("RAX", 4, 8),
                a: make_var("RAX", 3, 8),
                b: make_var("const:3", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("RDX", 2, 8),
                src: make_var("RAX", 4, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 1, 8),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("RAX", 5, 8),
                src: make_var("tmp:11f80", 1, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("RDX", 3, 8),
                a: make_var("RDX", 2, 8),
                b: make_var("RAX", 5, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 4, 8),
                a: make_var("RDX", 3, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 4, 8),
                val: make_var("EDX", 0, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 5, 8),
                a: make_var("RDX", 3, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("ECX", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 5, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 6, 8),
                a: make_var("RDX", 3, 8),
                b: make_var("const:34", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("EAX", 2, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 6, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("EAX", 3, 4),
                a: make_var("EAX", 2, 4),
                b: make_var("ECX", 1, 4),
            },
            SSAOp::Return {
                target: make_var("RIP", 0, 8),
            },
        ]);

        let mut ctx = make_x86_64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arr".to_string()),
                ("esi".to_string(), "idx".to_string()),
                ("edx".to_string(), "v".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                (
                    "arr".to_string(),
                    CType::ptr(CType::Struct("DemoStruct".to_string())),
                ),
                ("idx".to_string(), CType::Int(32)),
                ("v".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demostruct".to_string(),
                ExternalStruct {
                    name: "DemoStruct".to_string(),
                    fields: [
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
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));

        ctx.analyze_block(&block);

        let load_8 = {
            let mut visited = HashSet::new();
            ctx.render_semantic_value_by_name("ECX_1", 0, &mut visited)
        };
        let load_34 = {
            let mut visited = HashSet::new();
            ctx.render_semantic_value_by_name("EAX_2", 0, &mut visited)
        };
        let expr_8 = ctx.get_expr(&make_var("ECX", 1, 4));
        let expr_34 = ctx.get_expr(&make_var("EAX", 2, 4));

        assert!(
            matches!(
                ctx.lookup_semantic_value("ECX_1"),
                Some(crate::analysis::SemanticValue::Load { .. })
            ),
            "expected semantic load for ECX_1, got {:?}",
            ctx.lookup_semantic_value("ECX_1")
        );
        assert!(
            matches!(
                ctx.lookup_semantic_value("EAX_2"),
                Some(crate::analysis::SemanticValue::Load { .. })
            ),
            "expected semantic load for EAX_2, got {:?}",
            ctx.lookup_semantic_value("EAX_2")
        );
        assert!(
            matches!(load_8, Some(CExpr::Member { .. } | CExpr::PtrMember { .. })),
            "expected ECX_1 load to render as indexed member, got {load_8:?}"
        );
        assert!(
            matches!(
                load_34,
                Some(CExpr::Member { .. } | CExpr::PtrMember { .. })
            ),
            "expected EAX_2 load to render as indexed member, got {load_34:?}"
        );
        assert!(
            matches!(expr_8, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected get_expr(ECX_1) to keep indexed member render, got {expr_8:?}; semantic={load_8:?}"
        );
        assert!(
            matches!(expr_34, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected get_expr(EAX_2) to keep indexed member render, got {expr_34:?}; semantic={load_34:?}"
        );
    }

    #[test]
    fn test_get_return_expr_keeps_negative_index_subscript() {
        let idx = make_var("ESI", 0, 4);
        let arr = make_var("RDI", 0, 8);
        let ret = make_var("EAX", 1, 4);
        let mut ctx = FoldingContext::new(64);
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                ("arg1".to_string(), CType::ptr(CType::Int(32))),
                ("arg2".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            ret.display_name(),
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(arr)),
                    index: Some(crate::analysis::ValueRef::from(idx)),
                    scale_bytes: -4,
                    offset_bytes: 0,
                },
                size: 4,
            },
        );

        let expr = ctx.get_return_expr(&ret);
        let rendered = format!("{expr:?}");
        assert!(
            rendered.contains("Subscript"),
            "expected negative indexed load to stay a subscript, got {expr:?}"
        );
        assert!(
            rendered.contains("Neg") || rendered.contains("0 -") || rendered.contains("arg2"),
            "expected semantic negative index, got {expr:?}"
        );
    }

    #[test]
    fn test_observed_x86_negative_index_stack_reload_keeps_semantic_subscript() {
        let rbp = make_var("RBP", 0, 8);
        let rdi = make_var("RDI", 0, 8);
        let esi = make_var("ESI", 0, 4);
        let ecx0 = make_var("ECX", 0, 4);
        let slot_arr = make_var("tmp:4700", 1, 8);
        let slot_idx = make_var("tmp:4700", 2, 8);
        let arr_loaded = make_var("tmp:11f80", 1, 8);
        let rax1 = make_var("RAX", 1, 8);
        let zeroed = make_var("ECX", 1, 4);
        let idx_loaded = make_var("tmp:11f00", 3, 4);
        let neg_idx = make_var("ECX", 2, 4);
        let sext_idx = make_var("RCX", 3, 8);
        let scaled = make_var("tmp:4900", 1, 8);
        let addr = make_var("tmp:4a00", 1, 8);
        let load = make_var("tmp:11f00", 4, 4);
        let ret = make_var("EAX", 1, 4);

        let mut ctx = FoldingContext::new(64);
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                ("arg1".to_string(), CType::ptr(CType::Int(32))),
                ("arg2".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: slot_arr.clone(),
                a: rbp.clone(),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: slot_arr.clone(),
                val: rdi,
            },
            SSAOp::IntAdd {
                dst: slot_idx.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: slot_idx.clone(),
                val: esi,
            },
            SSAOp::Load {
                dst: arr_loaded.clone(),
                space: "ram".to_string(),
                addr: slot_arr,
            },
            SSAOp::Copy {
                dst: rax1.clone(),
                src: arr_loaded,
            },
            SSAOp::IntXor {
                dst: zeroed.clone(),
                a: ecx0.clone(),
                b: ecx0,
            },
            SSAOp::Load {
                dst: idx_loaded.clone(),
                space: "ram".to_string(),
                addr: slot_idx,
            },
            SSAOp::IntSub {
                dst: neg_idx.clone(),
                a: zeroed,
                b: idx_loaded,
            },
            SSAOp::IntSExt {
                dst: sext_idx.clone(),
                src: neg_idx,
            },
            SSAOp::IntMult {
                dst: scaled.clone(),
                a: sext_idx,
                b: make_var("const:4", 0, 8),
            },
            SSAOp::IntAdd {
                dst: addr.clone(),
                a: rax1,
                b: scaled,
            },
            SSAOp::Load {
                dst: load.clone(),
                space: "ram".to_string(),
                addr,
            },
            SSAOp::Copy {
                dst: ret.clone(),
                src: load,
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let inner_access = ctx.debug_render_memory_access_from_visible_expr(
            &CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("arg1".to_string()),
                CExpr::binary(
                    BinaryOp::Mul,
                    CExpr::binary(
                        BinaryOp::Sub,
                        CExpr::binary(
                            BinaryOp::BitXor,
                            CExpr::Var("arg4".to_string()),
                            CExpr::Var("arg4".to_string()),
                        ),
                        CExpr::Var("arg2".to_string()),
                    ),
                    CExpr::IntLit(4),
                ),
            ),
            4,
        );
        let normalized = ctx.debug_normalized_addr_from_visible_expr(&CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("arg1".to_string()),
            CExpr::binary(
                BinaryOp::Mul,
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::binary(
                        BinaryOp::BitXor,
                        CExpr::Var("arg4".to_string()),
                        CExpr::Var("arg4".to_string()),
                    ),
                    CExpr::Var("arg2".to_string()),
                ),
                CExpr::IntLit(4),
            ),
        ));
        let canonical = ctx.debug_canonicalize_visible_address_expr(&CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("arg1".to_string()),
            CExpr::binary(
                BinaryOp::Mul,
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::binary(
                        BinaryOp::BitXor,
                        CExpr::Var("arg4".to_string()),
                        CExpr::Var("arg4".to_string()),
                    ),
                    CExpr::Var("arg2".to_string()),
                ),
                CExpr::IntLit(4),
            ),
        ));
        let extracted = ctx.debug_extract_visible_scaled_index(&CExpr::binary(
            BinaryOp::Mul,
            CExpr::binary(
                BinaryOp::Sub,
                CExpr::IntLit(0),
                CExpr::Var("arg2".to_string()),
            ),
            CExpr::IntLit(4),
        ));
        let base_norm =
            ctx.debug_normalized_addr_from_visible_expr(&CExpr::Var("arg1".to_string()));
        let idx_norm = ctx.debug_normalized_addr_from_visible_expr(&CExpr::Var("arg2".to_string()));
        let arg1_ssa = ctx.debug_ssa_var_for_visible_name("arg1");
        let arg2_ssa = ctx.debug_ssa_var_for_visible_name("arg2");
        let arg4_ssa = ctx.debug_ssa_var_for_visible_name("arg4");
        let stages = ctx.debug_return_expr_stages(&ret);
        let expr = ctx.get_return_expr(&ret);
        let rendered = format!("{expr:?}");
        assert!(
            matches!(expr, CExpr::Subscript { .. }),
            "expected observed x86 negative-index load to render as subscript, got {expr:?}, stages={stages:?}, canonical={canonical:?}, extracted={extracted:?}, normalized={normalized:?}, inner_access={inner_access:?}, base_norm={base_norm:?}, idx_norm={idx_norm:?}, arg1_ssa={arg1_ssa:?}, arg2_ssa={arg2_ssa:?}, arg4_ssa={arg4_ssa:?}"
        );
        assert!(
            rendered.contains("Neg") || rendered.contains("arg2"),
            "expected semantic negative index in observed x86 shape, got {expr:?}"
        );
    }

    #[test]
    fn test_observed_x86_positive_index_stack_reload_keeps_semantic_subscript() {
        let rbp = make_var("RBP", 0, 8);
        let rdi = make_var("RDI", 0, 8);
        let esi = make_var("ESI", 0, 4);
        let slot_arr = make_var("tmp:4700", 1, 8);
        let slot_idx = make_var("tmp:4700", 2, 8);
        let arr_loaded = make_var("tmp:11f80", 1, 8);
        let rax1 = make_var("RAX", 1, 8);
        let idx_loaded = make_var("tmp:11f00", 1, 4);
        let eax1 = make_var("EAX", 1, 4);
        let sext_idx = make_var("RAX", 2, 8);
        let scaled = make_var("tmp:4900", 1, 8);
        let addr = make_var("tmp:4a00", 1, 8);
        let load = make_var("tmp:11f00", 2, 4);
        let ret = make_var("EAX", 2, 4);

        let mut ctx = FoldingContext::new(64);
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                ("arg1".to_string(), CType::ptr(CType::Int(32))),
                ("arg2".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: slot_arr.clone(),
                a: rbp.clone(),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: slot_arr.clone(),
                val: rdi,
            },
            SSAOp::IntAdd {
                dst: slot_idx.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: slot_idx.clone(),
                val: esi,
            },
            SSAOp::Load {
                dst: arr_loaded.clone(),
                space: "ram".to_string(),
                addr: slot_arr,
            },
            SSAOp::Copy {
                dst: rax1.clone(),
                src: arr_loaded,
            },
            SSAOp::Load {
                dst: idx_loaded.clone(),
                space: "ram".to_string(),
                addr: slot_idx,
            },
            SSAOp::Copy {
                dst: eax1.clone(),
                src: idx_loaded,
            },
            SSAOp::IntSExt {
                dst: sext_idx.clone(),
                src: eax1,
            },
            SSAOp::IntMult {
                dst: scaled.clone(),
                a: sext_idx,
                b: make_var("const:4", 0, 8),
            },
            SSAOp::IntAdd {
                dst: addr.clone(),
                a: rax1,
                b: scaled,
            },
            SSAOp::Load {
                dst: load.clone(),
                space: "ram".to_string(),
                addr,
            },
            SSAOp::Copy {
                dst: ret.clone(),
                src: load,
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let expr = ctx.get_return_expr(&ret);
        assert!(
            matches!(expr, CExpr::Subscript { .. }),
            "expected observed x86 positive-index load to render as subscript, got {expr:?}"
        );
        let rendered = format!("{expr:?}");
        assert!(
            rendered.contains("arg2"),
            "expected semantic positive index in observed x86 shape, got {expr:?}"
        );
    }

    #[test]
    fn test_observed_x86_negative_index_visible_expr_normalizes_to_negative_subscript() {
        let mut ctx = FoldingContext::new(64);
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
                ("ecx".to_string(), "ecx".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                ("arg1".to_string(), CType::ptr(CType::Int(32))),
                ("arg2".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert("ESI_0".to_string(), "arg2".to_string());
        ctx.state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert("ECX_1".to_string(), "ecx".to_string());
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "ecx".to_string(),
            CExpr::binary(
                BinaryOp::BitXor,
                CExpr::Var("ecx".to_string()),
                CExpr::Var("ecx".to_string()),
            ),
        );

        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("arg1".to_string()),
            CExpr::binary(
                BinaryOp::Mul,
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::binary(
                        BinaryOp::BitXor,
                        CExpr::Var("ecx".to_string()),
                        CExpr::Var("ecx".to_string()),
                    ),
                    CExpr::Var("arg2".to_string()),
                ),
                CExpr::IntLit(4),
            ),
        );

        let normalized = ctx
            .debug_normalized_addr_from_visible_expr(&expr)
            .expect("normalized address");
        assert_eq!(normalized.scale_bytes, -4, "{normalized:?}");

        let rendered = ctx
            .debug_render_memory_access_from_visible_expr(&expr, 4)
            .expect("semantic memory access");
        let text = format!("{rendered:?}");
        assert!(matches!(rendered, CExpr::Subscript { .. }), "{rendered:?}");
        assert!(
            text.contains("Neg") || text.contains("arg2"),
            "expected negative index in rendered access, got {rendered:?}"
        );
    }

    #[test]
    fn test_observed_x86_negative_index_visible_deref_promotes_to_subscript() {
        let mut ctx = FoldingContext::new(64);
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                ("arg1".to_string(), CType::ptr(CType::Int(32))),
                ("arg2".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        let raw = CExpr::Deref(Box::new(CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("arg1".to_string()),
            CExpr::binary(
                BinaryOp::Mul,
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::IntLit(0),
                    CExpr::Var("arg2".to_string()),
                ),
                CExpr::IntLit(4),
            ),
        )));

        let semantic = ctx.debug_semanticize_visible_expr(&raw);
        let text = format!("{semantic:?}");
        assert!(matches!(semantic, CExpr::Subscript { .. }), "{semantic:?}");
        assert!(
            text.contains("Neg") || text.contains("arg2"),
            "expected semantic negative subscript, got {semantic:?}"
        );
    }

    #[test]
    fn test_observed_x86_struct_field_return_uses_semantic_fields() {
        let rbp = make_var("RBP", 0, 8);
        let rdi = make_var("RDI", 0, 8);
        let esi = make_var("ESI", 0, 4);
        let slot_obj = make_var("tmp:4700", 1, 8);
        let slot_val = make_var("tmp:4700", 2, 8);
        let obj_loaded1 = make_var("tmp:11f80", 1, 8);
        let rax1 = make_var("RAX", 1, 8);
        let val_loaded = make_var("tmp:11f00", 1, 4);
        let ecx1 = make_var("ECX", 1, 4);
        let store_addr = make_var("tmp:4700", 3, 8);
        let obj_loaded2 = make_var("tmp:11f80", 2, 8);
        let rax2 = make_var("RAX", 2, 8);
        let load_addr30 = make_var("tmp:4700", 4, 8);
        let load30 = make_var("tmp:11f00", 2, 4);
        let eax1 = make_var("EAX", 1, 4);
        let load0 = make_var("tmp:11f00", 3, 4);
        let ret = make_var("EAX", 2, 4);

        let mut ctx = FoldingContext::new(64);
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                (
                    "arg1".to_string(),
                    CType::ptr(CType::Struct("DemoStruct".to_string())),
                ),
                ("arg2".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demostruct".to_string(),
                ExternalStruct {
                    name: "DemoStruct".to_string(),
                    fields: [
                        (
                            0,
                            ExternalField {
                                name: "f_0".to_string(),
                                offset: 0,
                                ty: Some("int32_t".to_string()),
                            },
                        ),
                        (
                            0x30,
                            ExternalField {
                                name: "f_30".to_string(),
                                offset: 0x30,
                                ty: Some("int32_t".to_string()),
                            },
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));
        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: slot_obj.clone(),
                a: rbp.clone(),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: slot_obj.clone(),
                val: rdi,
            },
            SSAOp::IntAdd {
                dst: slot_val.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: slot_val.clone(),
                val: esi,
            },
            SSAOp::Load {
                dst: val_loaded.clone(),
                space: "ram".to_string(),
                addr: slot_val,
            },
            SSAOp::Copy {
                dst: ecx1.clone(),
                src: val_loaded,
            },
            SSAOp::Load {
                dst: obj_loaded1.clone(),
                space: "ram".to_string(),
                addr: slot_obj.clone(),
            },
            SSAOp::Copy {
                dst: rax1.clone(),
                src: obj_loaded1,
            },
            SSAOp::IntAdd {
                dst: store_addr.clone(),
                a: rax1,
                b: make_var("const:30", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: store_addr,
                val: ecx1,
            },
            SSAOp::Load {
                dst: obj_loaded2.clone(),
                space: "ram".to_string(),
                addr: slot_obj,
            },
            SSAOp::Copy {
                dst: rax2.clone(),
                src: obj_loaded2,
            },
            SSAOp::IntAdd {
                dst: load_addr30.clone(),
                a: rax2.clone(),
                b: make_var("const:30", 0, 8),
            },
            SSAOp::Load {
                dst: load30.clone(),
                space: "ram".to_string(),
                addr: load_addr30,
            },
            SSAOp::Copy {
                dst: eax1.clone(),
                src: load30,
            },
            SSAOp::Load {
                dst: load0.clone(),
                space: "ram".to_string(),
                addr: rax2.clone(),
            },
            SSAOp::IntAdd {
                dst: ret.clone(),
                a: eax1,
                b: load0.clone(),
            },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let expr = ctx.get_return_expr(&ret);
        let rendered = format!("{expr:?}");
        assert!(
            rendered.contains("f_30") && rendered.contains("f_0"),
            "expected observed x86 struct return to use both fields, got {expr:?}"
        );
        assert!(
            !rendered.contains("IntLit(48)") && !rendered.contains("Deref"),
            "raw pointer math should not survive observed x86 struct-field return, got {expr:?}"
        );
    }

    #[test]
    fn test_observed_x86_struct_field_visible_deref_promotes_to_member() {
        let mut ctx = FoldingContext::new(64);
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [(
                "arg1".to_string(),
                CType::ptr(CType::Struct("DemoStruct".to_string())),
            )]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demostruct".to_string(),
                ExternalStruct {
                    name: "DemoStruct".to_string(),
                    fields: [
                        (
                            0,
                            ExternalField {
                                name: "f_0".to_string(),
                                offset: 0,
                                ty: Some("int32_t".to_string()),
                            },
                        ),
                        (
                            0x30,
                            ExternalField {
                                name: "f_30".to_string(),
                                offset: 0x30,
                                ty: Some("int32_t".to_string()),
                            },
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));

        let raw = CExpr::Deref(Box::new(CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("arg1".to_string()),
            CExpr::IntLit(0x30),
        )));
        let semantic = ctx.debug_semanticize_visible_expr(&raw);
        let text = format!("{semantic:?}");
        assert!(
            text.contains("f_30"),
            "expected visible raw deref to promote to f_30, got {semantic:?}"
        );
        assert!(!text.contains("Deref"), "{semantic:?}");
    }

    #[test]
    fn test_observed_live_arm64_struct_field_store_does_not_reinterpret_stack_slot_as_member_zero()
    {
        let sp0 = make_var("SP", 0, 8);
        let sp1 = make_var("SP", 1, 8);
        let x0 = make_var("X0", 0, 8);
        let w1 = make_var("W1", 0, 4);
        let slot_obj = make_var("tmp:6500", 1, 8);
        let slot_val = make_var("tmp:6400", 1, 8);
        let load_val = make_var("tmp:24c00", 1, 4);
        let x8_1 = make_var("X8", 1, 8);
        let slot_obj_2 = make_var("tmp:6500", 2, 8);
        let x9_1 = make_var("X9", 1, 8);
        let field_addr_30 = make_var("tmp:6400", 3, 8);
        let slot_obj_3 = make_var("tmp:6500", 3, 8);
        let x8_2 = make_var("X8", 2, 8);
        let field_addr_30_load = make_var("tmp:6400", 4, 8);
        let load_30 = make_var("tmp:24c00", 2, 4);
        let x8_3 = make_var("X8", 3, 8);
        let slot_obj_4 = make_var("tmp:6500", 4, 8);
        let x9_2 = make_var("X9", 2, 8);
        let copy_base = make_var("tmp:6780", 1, 8);
        let load_0 = make_var("tmp:24c00", 3, 4);
        let w9_0 = make_var("W9", 0, 4);
        let add_tmp = make_var("tmp:12280", 1, 4);
        let x0_1 = make_var("X0", 1, 8);
        let pc_1 = make_var("PC", 1, 8);
        let x30_0 = make_var("X30", 0, 8);

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [
                ("x0".to_string(), "arg1".to_string()),
                ("x1".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        ));
        ctx.set_type_hints(
            [
                (
                    "arg1".to_string(),
                    CType::ptr(CType::Struct("sla_struct_081b815e29a27703".to_string())),
                ),
                ("arg2".to_string(), CType::Int(32)),
            ]
            .into_iter()
            .collect(),
        );
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "sla_struct_081b815e29a27703".to_string(),
                ExternalStruct {
                    name: "sla_struct_081b815e29a27703".to_string(),
                    fields: [
                        (
                            0,
                            ExternalField {
                                name: "f_0".to_string(),
                                offset: 0,
                                ty: Some("int32_t".to_string()),
                            },
                        ),
                        (
                            0x30,
                            ExternalField {
                                name: "f_30".to_string(),
                                offset: 0x30,
                                ty: Some("int64_t".to_string()),
                            },
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));

        let block = make_block(vec![
            SSAOp::IntSub {
                dst: sp1.clone(),
                a: sp0,
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntAdd {
                dst: slot_obj.clone(),
                a: sp1.clone(),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: slot_obj,
                val: x0,
            },
            SSAOp::IntAdd {
                dst: slot_val.clone(),
                a: sp1.clone(),
                b: make_var("const:4", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: slot_val,
                val: w1,
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 2, 8),
                a: sp1.clone(),
                b: make_var("const:4", 0, 8),
            },
            SSAOp::Load {
                dst: load_val.clone(),
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 2, 8),
            },
            SSAOp::IntZExt {
                dst: x8_1.clone(),
                src: load_val,
            },
            SSAOp::IntAdd {
                dst: slot_obj_2.clone(),
                a: sp1.clone(),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Load {
                dst: x9_1.clone(),
                space: "ram".to_string(),
                addr: slot_obj_2,
            },
            SSAOp::IntAdd {
                dst: field_addr_30.clone(),
                a: x9_1,
                b: make_var("const:30", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: field_addr_30,
                val: make_var("W8", 0, 4),
            },
            SSAOp::IntAdd {
                dst: slot_obj_3.clone(),
                a: sp1.clone(),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Load {
                dst: x8_2.clone(),
                space: "ram".to_string(),
                addr: slot_obj_3,
            },
            SSAOp::IntAdd {
                dst: field_addr_30_load.clone(),
                a: x8_2.clone(),
                b: make_var("const:30", 0, 8),
            },
            SSAOp::Load {
                dst: load_30.clone(),
                space: "ram".to_string(),
                addr: field_addr_30_load,
            },
            SSAOp::IntZExt {
                dst: x8_3,
                src: load_30,
            },
            SSAOp::IntAdd {
                dst: slot_obj_4.clone(),
                a: sp1,
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Load {
                dst: x9_2.clone(),
                space: "ram".to_string(),
                addr: slot_obj_4,
            },
            SSAOp::Copy {
                dst: copy_base.clone(),
                src: x9_2,
            },
            SSAOp::Load {
                dst: load_0.clone(),
                space: "ram".to_string(),
                addr: copy_base,
            },
            SSAOp::Copy {
                dst: make_var("tmp:12180", 1, 4),
                src: w9_0,
            },
            SSAOp::IntAdd {
                dst: add_tmp.clone(),
                a: make_var("W8", 0, 4),
                b: make_var("tmp:12180", 1, 4),
            },
            SSAOp::IntZExt {
                dst: x0_1,
                src: add_tmp,
            },
            SSAOp::Copy {
                dst: pc_1.clone(),
                src: x30_0,
            },
            SSAOp::Return { target: pc_1 },
        ]);

        ctx.analyze_blocks(std::slice::from_ref(&block));
        ctx.state.return_blocks.insert(block.addr);
        let stmts = ctx.fold_block(&block, block.addr);
        let text = format!("{stmts:?}");
        assert!(
            !text.contains("f_0 = Var(\"x0\")"),
            "entry arg root spill should not survive as field store, got {stmts:?}"
        );
        assert!(
            text.contains("f_30"),
            "expected semantic field store in observed arm64 struct field case, got {stmts:?}"
        );
    }

    #[test]
    fn test_live_arm64_check_secret_then_block_folds_to_return_zero() {
        use r2il::R2ILBlock;
        use r2ssa::{PhiNode, SSAFunction};

        let mut b0 = R2ILBlock::new(0x1000, 4);
        b0.push(R2ILOp::CBranch {
            target: Varnode::constant(0x100c, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut b_fallthrough = R2ILBlock::new(0x1004, 4);
        b_fallthrough.push(R2ILOp::Branch {
            target: Varnode::constant(0x1008, 8),
        });
        let mut b_else = R2ILBlock::new(0x1008, 4);
        b_else.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut b_then = R2ILBlock::new(0x100c, 4);
        b_then.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut b_exit = R2ILBlock::new(0x1010, 4);
        b_exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let blocks = vec![b0, b_fallthrough, b_else, b_then, b_exit];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");

        func.get_block_mut(0x1000).expect("entry").ops = vec![SSAOp::CBranch {
            target: make_var("ram:1020", 0, 8),
            cond: make_var("tmp:a00", 1, 1),
        }];
        func.get_block_mut(0x1004).expect("fallthrough").ops = vec![SSAOp::Branch {
            target: make_var("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("else").ops = vec![
            SSAOp::Copy {
                dst: make_var("X8", 3, 8),
                src: make_var("const:1", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 3, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 3, 8),
                val: make_var("W8", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1010", 0, 8),
            },
        ];
        func.get_block_mut(0x100c).expect("then").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 4, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 4, 8),
                val: make_var("const:0", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1010", 0, 8),
            },
        ];
        let exit = func.get_block_mut(0x1010).expect("exit");
        exit.phis = vec![
            PhiNode {
                dst: make_var("X8", 4, 8),
                sources: vec![
                    (0x100c, make_var("X8", 0, 8)),
                    (0x1008, make_var("X8", 0, 8)),
                ],
            },
            PhiNode {
                dst: make_var("tmp:300", 2, 4),
                sources: vec![
                    (0x100c, make_var("tmp:300", 0, 4)),
                    (0x1008, make_var("tmp:300", 0, 4)),
                ],
            },
            PhiNode {
                dst: make_var("tmp:6400", 5, 8),
                sources: vec![
                    (0x100c, make_var("tmp:6400", 0, 8)),
                    (0x1008, make_var("tmp:6400", 0, 8)),
                ],
            },
        ];
        exit.ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 6, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:24c00", 2, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 6, 8),
            },
            SSAOp::IntZExt {
                dst: make_var("X0", 1, 8),
                src: make_var("tmp:24c00", 2, 4),
            },
            SSAOp::Copy {
                dst: make_var("PC", 1, 8),
                src: make_var("X30", 0, 8),
            },
            SSAOp::Return {
                target: make_var("PC", 1, 8),
            },
        ];

        let mut ctx = make_aarch64_ctx();
        ctx.analyze_blocks(&func.blocks().cloned().collect::<Vec<_>>());
        ctx.analyze_function_structure(&func);

        assert!(ctx.state.return_blocks.contains(&0x100c));
        assert!(ctx.state.return_blocks.contains(&0x1008));
        assert!(ctx.state.return_stack_slots.contains(&12));

        let then_block = func.get_block(0x100c).expect("then block");
        let then_stmts = ctx.fold_block(then_block, then_block.addr);
        let Some(CStmt::Return(Some(expr))) = then_stmts.last() else {
            panic!("expected trailing return in then block, got {then_stmts:?}");
        };
        assert_eq!(expr, &CExpr::IntLit(0));
    }

    #[test]
    fn test_observed_live_arm64_check_secret_then_block_folds_to_return_zero() {
        use r2il::R2ILBlock;
        use r2ssa::{PhiNode, SSAFunction};

        let mut b0 = R2ILBlock::new(0x1000, 4);
        b0.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1020, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut b_fallthrough = R2ILBlock::new(0x1004, 4);
        b_fallthrough.push(R2ILOp::Branch {
            target: Varnode::constant(0x1008, 8),
        });
        let mut b_else = R2ILBlock::new(0x1008, 4);
        b_else.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut b_then = R2ILBlock::new(0x1020, 4);
        b_then.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut b_exit = R2ILBlock::new(0x1010, 4);
        b_exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let blocks = vec![b0, b_fallthrough, b_else, b_then, b_exit];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");

        func.get_block_mut(0x1000).expect("entry").ops = vec![SSAOp::CBranch {
            target: make_var("ram:1020", 0, 8),
            cond: make_var("tmp:a00", 1, 1),
        }];
        func.get_block_mut(0x1004).expect("fallthrough").ops = vec![SSAOp::Branch {
            target: make_var("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("else").ops = vec![
            SSAOp::Copy {
                dst: make_var("X8", 3, 8),
                src: make_var("const:1", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 3, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 3, 8),
                val: make_var("W8", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1010", 0, 8),
            },
        ];
        func.get_block_mut(0x1020).expect("then").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 6, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:300", 2, 4),
                src: make_var("const:0", 0, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 6, 8),
                val: make_var("const:0", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1010", 0, 8),
            },
        ];
        let exit = func.get_block_mut(0x1010).expect("exit");
        exit.phis = vec![
            PhiNode {
                dst: make_var("tmp:300", 1, 4),
                sources: vec![
                    (0x1020, make_var("const:0", 0, 4)),
                    (0x1008, make_var("tmp:300", 0, 4)),
                ],
            },
            PhiNode {
                dst: make_var("tmp:6400", 4, 8),
                sources: vec![
                    (0x1020, make_var("tmp:6400", 6, 8)),
                    (0x1008, make_var("tmp:6400", 0, 8)),
                ],
            },
            PhiNode {
                dst: make_var("X8", 4, 8),
                sources: vec![
                    (0x1020, make_var("X8", 2, 8)),
                    (0x1008, make_var("X8", 0, 8)),
                ],
            },
        ];
        exit.ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 5, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:24c00", 2, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 5, 8),
            },
            SSAOp::IntZExt {
                dst: make_var("X0", 1, 8),
                src: make_var("tmp:24c00", 2, 4),
            },
            SSAOp::Copy {
                dst: make_var("tmp:11e80", 1, 8),
                src: make_var("const:10", 0, 8),
            },
            SSAOp::IntCarry {
                dst: make_var("TMPCY", 2, 1),
                a: make_var("SP", 1, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntSCarry {
                dst: make_var("TMPOV", 2, 1),
                a: make_var("SP", 1, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:11f80", 1, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntSLess {
                dst: make_var("TMPNG", 2, 1),
                a: make_var("tmp:11f80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntEqual {
                dst: make_var("TMPZR", 2, 1),
                a: make_var("tmp:11f80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("SP", 2, 8),
                src: make_var("tmp:11f80", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("PC", 1, 8),
                src: make_var("X30", 0, 8),
            },
            SSAOp::Return {
                target: make_var("PC", 1, 8),
            },
        ];

        let mut ctx = make_aarch64_ctx();
        ctx.analyze_blocks(&func.blocks().cloned().collect::<Vec<_>>());
        ctx.analyze_function_structure(&func);

        let then_block = func.get_block(0x1020).expect("then block");
        let then_stmts = ctx.fold_block(then_block, then_block.addr);
        let Some(CStmt::Return(Some(expr))) = then_stmts.last() else {
            panic!("expected trailing return in observed then block, got {then_stmts:?}");
        };
        assert_eq!(expr, &CExpr::IntLit(0));
    }

    #[test]
    fn test_observed_live_arm64_check_secret_full_decompile_returns_zero_and_one() {
        use r2il::R2ILBlock;
        use r2ssa::{PhiNode, SSAFunction};

        let mut b0 = R2ILBlock::new(0x1000, 4);
        b0.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1028, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut b_fallthrough = R2ILBlock::new(0x1004, 4);
        b_fallthrough.push(R2ILOp::Branch {
            target: Varnode::constant(0x1014, 8),
        });
        let mut b_else = R2ILBlock::new(0x1014, 4);
        b_else.push(R2ILOp::Branch {
            target: Varnode::constant(0x1030, 8),
        });
        let mut b_then = R2ILBlock::new(0x1028, 4);
        b_then.push(R2ILOp::Branch {
            target: Varnode::constant(0x1030, 8),
        });
        let mut b_exit = R2ILBlock::new(0x1030, 4);
        b_exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let blocks = vec![b0, b_fallthrough, b_else, b_then, b_exit];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        func = func.with_name("sym._check_secret");
        assert_eq!(func.successors(0x1014), vec![0x1030]);

        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntSub {
                dst: make_var("SP", 1, 8),
                a: make_var("SP", 0, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 1, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 1, 8),
                val: make_var("W0", 0, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 2, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:24c00", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 2, 8),
            },
            SSAOp::IntZExt {
                dst: make_var("X8", 1, 8),
                src: make_var("tmp:24c00", 1, 4),
            },
            SSAOp::Copy {
                dst: make_var("X9", 1, 8),
                src: make_var("const:dead", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:3e480", 1, 4),
                src: make_var("W9", 0, 4),
            },
            SSAOp::IntLessEqual {
                dst: make_var("TMPCY", 1, 1),
                a: make_var("tmp:3e480", 1, 4),
                b: make_var("W8", 0, 4),
            },
            SSAOp::IntSBorrow {
                dst: make_var("TMPOV", 1, 1),
                a: make_var("W8", 0, 4),
                b: make_var("tmp:3e480", 1, 4),
            },
            SSAOp::IntSub {
                dst: make_var("tmp:3e580", 1, 4),
                a: make_var("W8", 0, 4),
                b: make_var("tmp:3e480", 1, 4),
            },
            SSAOp::IntSLess {
                dst: make_var("TMPNG", 1, 1),
                a: make_var("tmp:3e580", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("TMPZR", 1, 1),
                a: make_var("tmp:3e580", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntZExt {
                dst: make_var("X8", 2, 8),
                src: make_var("tmp:3e580", 1, 4),
            },
            SSAOp::Copy {
                dst: make_var("NG", 1, 1),
                src: make_var("TMPNG", 1, 1),
            },
            SSAOp::Copy {
                dst: make_var("ZR", 1, 1),
                src: make_var("TMPZR", 1, 1),
            },
            SSAOp::Copy {
                dst: make_var("CY", 1, 1),
                src: make_var("TMPCY", 1, 1),
            },
            SSAOp::Copy {
                dst: make_var("OV", 1, 1),
                src: make_var("TMPOV", 1, 1),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:a00", 1, 1),
                src: make_var("ZR", 1, 1),
            },
            SSAOp::CBranch {
                target: make_var("ram:1028", 0, 8),
                cond: make_var("tmp:a00", 1, 1),
            },
        ];
        func.get_block_mut(0x1004).expect("fallthrough").ops = vec![SSAOp::Branch {
            target: make_var("ram:1014", 0, 8),
        }];
        func.get_block_mut(0x1014).expect("else").ops = vec![
            SSAOp::Copy {
                dst: make_var("X8", 3, 8),
                src: make_var("const:1", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 4, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 4, 8),
                val: make_var("const:1", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1030", 0, 8),
            },
        ];
        func.get_block_mut(0x1028).expect("then").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 3, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:300", 1, 4),
                src: make_var("const:0", 0, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 3, 8),
                val: make_var("const:0", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1030", 0, 8),
            },
        ];
        let exit = func.get_block_mut(0x1030).expect("exit");
        exit.phis = vec![
            PhiNode {
                dst: make_var("tmp:300", 2, 4),
                sources: vec![
                    (0x1028, make_var("tmp:300", 0, 4)),
                    (0x1014, make_var("tmp:300", 0, 4)),
                ],
            },
            PhiNode {
                dst: make_var("X8", 4, 8),
                sources: vec![
                    (0x1028, make_var("X8", 0, 8)),
                    (0x1014, make_var("X8", 0, 8)),
                ],
            },
            PhiNode {
                dst: make_var("tmp:6400", 5, 8),
                sources: vec![
                    (0x1028, make_var("tmp:6400", 0, 8)),
                    (0x1014, make_var("tmp:6400", 0, 8)),
                ],
            },
        ];
        exit.ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 6, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:24c00", 2, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 6, 8),
            },
            SSAOp::IntZExt {
                dst: make_var("X0", 1, 8),
                src: make_var("tmp:24c00", 2, 4),
            },
            SSAOp::Copy {
                dst: make_var("tmp:11e80", 1, 8),
                src: make_var("const:10", 0, 8),
            },
            SSAOp::IntCarry {
                dst: make_var("TMPCY", 2, 1),
                a: make_var("SP", 1, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntSCarry {
                dst: make_var("TMPOV", 2, 1),
                a: make_var("SP", 1, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:11f80", 1, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntSLess {
                dst: make_var("TMPNG", 2, 1),
                a: make_var("tmp:11f80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntEqual {
                dst: make_var("TMPZR", 2, 1),
                a: make_var("tmp:11f80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("SP", 2, 8),
                src: make_var("tmp:11f80", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("PC", 1, 8),
                src: make_var("X30", 0, 8),
            },
            SSAOp::Return {
                target: make_var("PC", 1, 8),
            },
        ];

        let decompiler = crate::Decompiler::new(crate::DecompilerConfig::aarch64());
        let output = decompiler.decompile(&func);
        assert!(
            output.contains("return 0;") && output.contains("return 1;"),
            "expected concrete merged returns, got:\n{output}"
        );
        assert!(
            !output.contains("&stack"),
            "structured merge return must not degrade to &stack, got:\n{output}"
        );
    }

    #[test]
    fn test_observed_live_arm64_check_secret_with_plugin_context_returns_zero_and_one() {
        use r2il::R2ILBlock;
        use r2ssa::{PhiNode, SSAFunction};

        let mut b0 = R2ILBlock::new(0x1000, 4);
        b0.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1028, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut b_fallthrough = R2ILBlock::new(0x1004, 4);
        b_fallthrough.push(R2ILOp::Branch {
            target: Varnode::constant(0x1014, 8),
        });
        let mut b_else = R2ILBlock::new(0x1014, 4);
        b_else.push(R2ILOp::Branch {
            target: Varnode::constant(0x1030, 8),
        });
        let mut b_then = R2ILBlock::new(0x1028, 4);
        b_then.push(R2ILOp::Branch {
            target: Varnode::constant(0x1030, 8),
        });
        let mut b_exit = R2ILBlock::new(0x1030, 4);
        b_exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let blocks = vec![b0, b_fallthrough, b_else, b_then, b_exit];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        func = func.with_name("sym._check_secret");
        assert_eq!(func.successors(0x1014), vec![0x1030]);

        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntSub {
                dst: make_var("SP", 1, 8),
                a: make_var("SP", 0, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 1, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 1, 8),
                val: make_var("W0", 0, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 2, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:24c00", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 2, 8),
            },
            SSAOp::IntZExt {
                dst: make_var("X8", 1, 8),
                src: make_var("tmp:24c00", 1, 4),
            },
            SSAOp::Copy {
                dst: make_var("X9", 1, 8),
                src: make_var("const:dead", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:3e480", 1, 4),
                src: make_var("W9", 0, 4),
            },
            SSAOp::IntLessEqual {
                dst: make_var("TMPCY", 1, 1),
                a: make_var("tmp:3e480", 1, 4),
                b: make_var("W8", 0, 4),
            },
            SSAOp::IntSBorrow {
                dst: make_var("TMPOV", 1, 1),
                a: make_var("W8", 0, 4),
                b: make_var("tmp:3e480", 1, 4),
            },
            SSAOp::IntSub {
                dst: make_var("tmp:3e580", 1, 4),
                a: make_var("W8", 0, 4),
                b: make_var("tmp:3e480", 1, 4),
            },
            SSAOp::IntSLess {
                dst: make_var("TMPNG", 1, 1),
                a: make_var("tmp:3e580", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("TMPZR", 1, 1),
                a: make_var("tmp:3e580", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntZExt {
                dst: make_var("X8", 2, 8),
                src: make_var("tmp:3e580", 1, 4),
            },
            SSAOp::Copy {
                dst: make_var("NG", 1, 1),
                src: make_var("TMPNG", 1, 1),
            },
            SSAOp::Copy {
                dst: make_var("ZR", 1, 1),
                src: make_var("TMPZR", 1, 1),
            },
            SSAOp::Copy {
                dst: make_var("CY", 1, 1),
                src: make_var("TMPCY", 1, 1),
            },
            SSAOp::Copy {
                dst: make_var("OV", 1, 1),
                src: make_var("TMPOV", 1, 1),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:a00", 1, 1),
                src: make_var("ZR", 1, 1),
            },
            SSAOp::CBranch {
                target: make_var("ram:1028", 0, 8),
                cond: make_var("tmp:a00", 1, 1),
            },
        ];
        func.get_block_mut(0x1004).expect("fallthrough").ops = vec![SSAOp::Branch {
            target: make_var("ram:1014", 0, 8),
        }];
        func.get_block_mut(0x1014).expect("else").ops = vec![
            SSAOp::Copy {
                dst: make_var("X8", 3, 8),
                src: make_var("const:1", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 4, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 4, 8),
                val: make_var("const:1", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1030", 0, 8),
            },
        ];
        func.get_block_mut(0x1028).expect("then").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 3, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:300", 1, 4),
                src: make_var("const:0", 0, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 3, 8),
                val: make_var("const:0", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1030", 0, 8),
            },
        ];
        let exit = func.get_block_mut(0x1030).expect("exit");
        exit.phis = vec![
            PhiNode {
                dst: make_var("tmp:300", 2, 4),
                sources: vec![
                    (0x1028, make_var("tmp:300", 0, 4)),
                    (0x1014, make_var("tmp:300", 0, 4)),
                ],
            },
            PhiNode {
                dst: make_var("X8", 4, 8),
                sources: vec![
                    (0x1028, make_var("X8", 0, 8)),
                    (0x1014, make_var("X8", 0, 8)),
                ],
            },
            PhiNode {
                dst: make_var("tmp:6400", 5, 8),
                sources: vec![
                    (0x1028, make_var("tmp:6400", 0, 8)),
                    (0x1014, make_var("tmp:6400", 0, 8)),
                ],
            },
        ];
        exit.ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 6, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:24c00", 2, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 6, 8),
            },
            SSAOp::IntZExt {
                dst: make_var("X0", 1, 8),
                src: make_var("tmp:24c00", 2, 4),
            },
            SSAOp::Copy {
                dst: make_var("tmp:11e80", 1, 8),
                src: make_var("const:10", 0, 8),
            },
            SSAOp::IntCarry {
                dst: make_var("TMPCY", 2, 1),
                a: make_var("SP", 1, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntSCarry {
                dst: make_var("TMPOV", 2, 1),
                a: make_var("SP", 1, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:11f80", 1, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntSLess {
                dst: make_var("TMPNG", 2, 1),
                a: make_var("tmp:11f80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntEqual {
                dst: make_var("TMPZR", 2, 1),
                a: make_var("tmp:11f80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("SP", 2, 8),
                src: make_var("tmp:11f80", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("PC", 1, 8),
                src: make_var("X30", 0, 8),
            },
            SSAOp::Return {
                target: make_var("PC", 1, 8),
            },
        ];

        let mut decompiler = crate::Decompiler::new(crate::DecompilerConfig::aarch64());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(crate::CType::Int(64)),
                vec![("arg1", Some(crate::CType::UInt(64)))],
            )),
            external_stack_vars: HashMap::from([
                (
                    8,
                    stack_var_spec("var_8h", Some(crate::CType::Int(64)), Some("sp")),
                ),
                (
                    12,
                    stack_var_spec("var_ch", Some(crate::CType::Int(32)), Some("sp")),
                ),
            ]),
            ..FunctionTypeFacts::default()
        });
        let output = decompiler.decompile(&func);
        assert!(
            output.contains("return 0;") && output.contains("return 1;"),
            "plugin-context merge return must stay concrete, got:\n{output}"
        );
        assert!(
            !output.contains("&arg1"),
            "plugin-context merge return must not degrade to &arg1, got:\n{output}"
        );
    }

    #[test]
    fn observed_live_arm64_imported_atoi_arg_uses_semantic_argv_root() {
        use crate::analysis::{PassEnv, StackInfo, UseInfo};

        let sp1 = make_var("SP", 1, 8);
        let frame_base = make_var("tmp:frame", 1, 8);
        let slot_178 = make_var("tmp:slot", 1, 8);
        let slot_argv = make_var("tmp:slot", 2, 8);
        let reload_slot = make_var("tmp:6500", 6, 8);
        let reloaded_frame = make_var("X8", 9, 8);
        let argv_addr = make_var("tmp:6500", 7, 8);
        let argv_root = make_var("X8", 10, 8);
        let arg_addr = make_var("tmp:6500", 8, 8);
        let arg_value = make_var("X0", 5, 8);

        let entry = SSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntSub {
                    dst: sp1.clone(),
                    a: make_var("SP", 0, 8),
                    b: make_var("const:10", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: frame_base.clone(),
                    a: sp1.clone(),
                    b: make_var("const:3e0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: slot_178.clone(),
                    a: sp1.clone(),
                    b: make_var("const:178", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: slot_178,
                    val: frame_base.clone(),
                },
                SSAOp::IntAdd {
                    dst: slot_argv.clone(),
                    a: frame_base,
                    b: make_var("const:a0", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: slot_argv,
                    val: make_var("X1", 0, 8),
                },
            ],
        };

        let call_block = SSABlock {
            addr: 0x1010,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: reload_slot.clone(),
                    a: sp1.clone(),
                    b: make_var("const:178", 0, 8),
                },
                SSAOp::Load {
                    dst: reloaded_frame.clone(),
                    space: "ram".to_string(),
                    addr: reload_slot,
                },
                SSAOp::IntAdd {
                    dst: argv_addr.clone(),
                    a: reloaded_frame,
                    b: make_var("const:a0", 0, 8),
                },
                SSAOp::Load {
                    dst: argv_root.clone(),
                    space: "ram".to_string(),
                    addr: argv_addr,
                },
                SSAOp::IntAdd {
                    dst: arg_addr.clone(),
                    a: argv_root.clone(),
                    b: make_var("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: arg_value.clone(),
                    space: "ram".to_string(),
                    addr: arg_addr,
                },
                SSAOp::Call {
                    target: make_var("const:401040", 0, 8),
                },
            ],
        };

        let mut function_names = HashMap::new();
        function_names.insert(0x401040, "sym.imp.atoi".to_string());
        let strings: HashMap<u64, String> = HashMap::new();
        let symbols: HashMap<u64, String> = HashMap::new();
        let param_register_aliases = HashMap::from([
            ("x0".to_string(), "argc".to_string()),
            ("x1".to_string(), "argv".to_string()),
            ("x2".to_string(), "envp".to_string()),
        ]);
        let type_hints =
            HashMap::from([("argv".to_string(), CType::ptr(CType::ptr(CType::Int(8))))]);
        let caller_saved_regs = HashSet::new();
        let arg_regs = vec![
            "x0".to_string(),
            "x1".to_string(),
            "x2".to_string(),
            "x3".to_string(),
            "x4".to_string(),
            "x5".to_string(),
            "x6".to_string(),
            "x7".to_string(),
        ];
        let env = PassEnv {
            ptr_size: 64,
            sp_name: "sp",
            fp_name: "x29",
            ret_reg_name: "x0",
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            callee_resolution: None,
            arg_regs: &arg_regs,
            param_register_aliases: &param_register_aliases,
            caller_saved_regs: &caller_saved_regs,
            type_hints: &type_hints,
            type_oracle: None,
        };

        let blocks = vec![entry, call_block];
        let use_info = UseInfo::analyze(&blocks, &env);
        let stack_info = StackInfo::analyze(&blocks, &use_info, &env);
        assert!(
            matches!(
                use_info.semantic_values.get("X8_10"),
                Some(crate::analysis::SemanticValue::Address(crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(value_ref),
                    index: None,
                    scale_bytes: 0,
                    offset_bytes: 0,
                })) if value_ref.var == make_var("X1", 0, 8)
            ),
            "expected argv root to stay semantic across blocks, got {:?}; stable_stack_values={:?}; type_hints={:?}; aliases={:?}",
            use_info.semantic_values.get("X8_10"),
            use_info.stable_stack_values,
            use_info.type_hints,
            use_info.var_aliases
        );
        assert!(
            matches!(
                use_info.semantic_values.get("X0_5"),
                Some(crate::analysis::SemanticValue::Load {
                    addr: crate::analysis::NormalizedAddr {
                        base: crate::analysis::BaseRef::Value(_),
                        ..
                    },
                    ..
                })
            ),
            "expected imported atoi arg load to keep value-rooted semantic addr, got {:?}",
            use_info.semantic_values.get("X0_5")
        );

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(function_names));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.atoi".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: false,
            },
        )]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(param_register_aliases));
        ctx.inputs.type_hints = Box::leak(Box::new(type_hints));
        ctx.state.analysis_ctx.use_info = use_info;
        ctx.state.analysis_ctx.stack_info = stack_info;

        let mut visited = HashSet::new();
        let semantic = ctx.render_semantic_value_by_name("X0_5", 0, &mut visited);
        assert!(
            semantic.is_some(),
            "expected semantic value for observed imported atoi arg load, got {:?}",
            ctx.state.analysis_ctx.use_info.semantic_values.get("X0_5")
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401040", 0, 8),
                },
                0x1010,
                6,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert!(
            matches!(
                &args[0],
                CExpr::Subscript { base, index }
                    if **base == CExpr::Var("argv".to_string()) && **index == CExpr::IntLit(1)
            ),
            "expected observed live arm64 atoi arg to render as argv[1], got: {:?}; semantic candidate: {:?}",
            args[0],
            semantic
        );
        assert!(
            !matches!(&args[0], CExpr::Deref(_)) && !expr_contains_var(&args[0], "lr"),
            "imported atoi arg should not regress to deref or transient register form, got: {:?}",
            args[0]
        );
    }

    #[test]
    fn observed_live_arm64_main_first_atoi_arg_renders_semantically() {
        let sp0 = make_var("SP", 0, 8);
        let sp1 = make_var("SP", 1, 8);
        let sp2 = make_var("SP", 2, 8);
        let fp_slot = make_var("tmp:7b80", 1, 8);
        let frame_base = make_var("tmp:11f80", 2, 8);
        let slot_178 = make_var("tmp:6500", 1, 8);
        let slot_argv = make_var("tmp:6500", 2, 8);
        let slot_local0 = make_var("tmp:6980", 1, 8);
        let slot_local1 = make_var("tmp:6980", 2, 8);
        let call_slot = make_var("tmp:6500", 5, 8);
        let call_frame = make_var("X8", 8, 8);
        let argv_addr = make_var("tmp:6500", 6, 8);
        let argv_root = make_var("X8", 9, 8);
        let arg_addr = make_var("tmp:6500", 7, 8);
        let arg_value = make_var("X0", 3, 8);

        let entry = SSABlock {
            addr: 0x100001308,
            size: 48,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: sp1.clone(),
                    a: sp0,
                    b: make_var("const:ffffffffffffffe0", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: sp1.clone(),
                    val: make_var("X28", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: make_var("tmp:3a600", 1, 8),
                    a: sp1.clone(),
                    b: make_var("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: make_var("tmp:3a600", 1, 8),
                    val: make_var("X27", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: fp_slot.clone(),
                    a: sp1.clone(),
                    b: make_var("const:10", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: fp_slot.clone(),
                    val: make_var("X29", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: make_var("tmp:3a600", 2, 8),
                    a: fp_slot.clone(),
                    b: make_var("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: make_var("tmp:3a600", 2, 8),
                    val: make_var("X30", 0, 8),
                },
                SSAOp::IntSub {
                    dst: sp2.clone(),
                    a: sp1.clone(),
                    b: make_var("const:550", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: frame_base.clone(),
                    a: sp2.clone(),
                    b: make_var("const:3e0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: slot_178.clone(),
                    a: sp2.clone(),
                    b: make_var("const:178", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: slot_178,
                    val: frame_base.clone(),
                },
                SSAOp::IntAdd {
                    dst: slot_local0,
                    a: fp_slot.clone(),
                    b: make_var("const:ffffffffffffffec", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: make_var("tmp:6980", 1, 8),
                    val: make_var("const:0", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("tmp:3a680", 2, 8),
                    src: make_var("W0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: slot_local1,
                    a: fp_slot.clone(),
                    b: make_var("const:ffffffffffffffe8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: make_var("tmp:6980", 2, 8),
                    val: make_var("tmp:3a680", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: slot_argv,
                    a: frame_base,
                    b: make_var("const:a0", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: make_var("tmp:6500", 2, 8),
                    val: make_var("X1", 0, 8),
                },
            ],
        };

        let call_block = SSABlock {
            addr: 0x100001368,
            size: 44,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: call_slot.clone(),
                    a: sp2.clone(),
                    b: make_var("const:178", 0, 8),
                },
                SSAOp::Load {
                    dst: call_frame.clone(),
                    space: "ram".to_string(),
                    addr: call_slot,
                },
                SSAOp::IntAdd {
                    dst: argv_addr.clone(),
                    a: call_frame,
                    b: make_var("const:a0", 0, 8),
                },
                SSAOp::Load {
                    dst: argv_root.clone(),
                    space: "ram".to_string(),
                    addr: argv_addr,
                },
                SSAOp::IntAdd {
                    dst: arg_addr.clone(),
                    a: argv_root.clone(),
                    b: make_var("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: arg_value.clone(),
                    space: "ram".to_string(),
                    addr: arg_addr,
                },
                SSAOp::Call {
                    target: make_var("const:1000025d8", 0, 8),
                },
            ],
        };

        let function_names = HashMap::from([(0x1000025d8, "sym.imp.atoi".to_string())]);
        let _strings: HashMap<u64, String> = HashMap::new();
        let _symbols: HashMap<u64, String> = HashMap::new();
        let param_register_aliases = HashMap::from([
            ("x0".to_string(), "argc".to_string()),
            ("x1".to_string(), "argv".to_string()),
            ("x2".to_string(), "envp".to_string()),
        ]);
        let type_hints = HashMap::from([
            ("argc".to_string(), CType::Int(32)),
            ("argv".to_string(), CType::ptr(CType::ptr(CType::Int(8)))),
            ("envp".to_string(), CType::ptr(CType::ptr(CType::Int(8)))),
        ]);
        let blocks = vec![entry, call_block];

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(function_names));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.atoi".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: false,
            },
        )]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(param_register_aliases));
        ctx.inputs.type_hints = Box::leak(Box::new(type_hints));
        ctx.analyze_blocks(&blocks);
        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:1000025d8", 0, 8),
                },
                0x100001368,
                6,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert!(
            matches!(
                &args[0],
                CExpr::Subscript { base, index }
                    if **base == CExpr::Var("argv".to_string()) && **index == CExpr::IntLit(1)
            ),
            "expected observed live main atoi arg to render as argv[1], got: {:?}",
            args[0]
        );

        let folded_stmts = ctx.fold_block(&blocks[1], blocks[1].addr);
        let folded_call_args = folded_stmts.iter().find_map(|stmt| {
            let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
                return None;
            };
            Some(args)
        });
        let Some(folded_call_args) = folded_call_args else {
            panic!("expected folded call statement, got {folded_stmts:?}");
        };
        assert!(
            matches!(
                folded_call_args.first(),
                Some(CExpr::Subscript { base, index })
                    if **base == CExpr::Var("argv".to_string()) && **index == CExpr::IntLit(1)
            ),
            "expected folded observed live main atoi arg to stay argv[1], got {folded_stmts:?}"
        );
    }

    #[test]
    fn observed_exact_live_arm64_main_first_atoi_arg_with_0x160_slot_renders_semantically() {
        let _sp0 = make_var("SP", 0, 8);
        let sp1 = make_var("SP", 1, 8);
        let sp2 = make_var("SP", 2, 8);
        let fp_slot = make_var("tmp:7b80", 1, 8);
        let frame_base = make_var("tmp:11f80", 2, 8);
        let slot_178 = make_var("tmp:6500", 1, 8);
        let slot_argv = make_var("tmp:6500", 2, 8);
        let call_slot = make_var("tmp:6500", 6, 8);
        let call_frame = make_var("X8", 9, 8);
        let argv_addr = make_var("tmp:6500", 7, 8);
        let argv_root = make_var("X8", 10, 8);
        let arg_addr = make_var("tmp:6500", 8, 8);
        let arg_value = make_var("X0", 5, 8);

        let entry = SSABlock {
            addr: 0x100001308,
            size: 48,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntSub {
                    dst: sp2.clone(),
                    a: sp1.clone(),
                    b: make_var("const:550", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: fp_slot.clone(),
                    a: sp1.clone(),
                    b: make_var("const:10", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: frame_base.clone(),
                    a: sp2.clone(),
                    b: make_var("const:3e0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: slot_178.clone(),
                    a: sp2.clone(),
                    b: make_var("const:178", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: slot_178,
                    val: frame_base.clone(),
                },
                SSAOp::IntAdd {
                    dst: slot_argv,
                    a: frame_base,
                    b: make_var("const:160", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: make_var("tmp:6500", 2, 8),
                    val: make_var("X1", 0, 8),
                },
            ],
        };

        let call_block = SSABlock {
            addr: 0x100001368,
            size: 44,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: call_slot.clone(),
                    a: sp2,
                    b: make_var("const:178", 0, 8),
                },
                SSAOp::Load {
                    dst: call_frame.clone(),
                    space: "ram".to_string(),
                    addr: call_slot,
                },
                SSAOp::IntAdd {
                    dst: argv_addr.clone(),
                    a: call_frame,
                    b: make_var("const:160", 0, 8),
                },
                SSAOp::Load {
                    dst: argv_root.clone(),
                    space: "ram".to_string(),
                    addr: argv_addr,
                },
                SSAOp::IntAdd {
                    dst: arg_addr.clone(),
                    a: argv_root,
                    b: make_var("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: arg_value,
                    space: "ram".to_string(),
                    addr: arg_addr,
                },
                SSAOp::Call {
                    target: make_var("const:1000025d8", 0, 8),
                },
            ],
        };

        let function_names = HashMap::from([(0x1000025d8, "sym.imp.atoi".to_string())]);
        let param_register_aliases = HashMap::from([
            ("x0".to_string(), "argc".to_string()),
            ("x1".to_string(), "argv".to_string()),
            ("x2".to_string(), "envp".to_string()),
        ]);
        let type_hints = HashMap::from([
            ("argc".to_string(), CType::Int(32)),
            ("argv".to_string(), CType::ptr(CType::ptr(CType::Int(8)))),
            ("envp".to_string(), CType::ptr(CType::ptr(CType::Int(8)))),
        ]);
        let caller_saved_regs = HashSet::new();
        let arg_regs = vec![
            "x0".to_string(),
            "x1".to_string(),
            "x2".to_string(),
            "x3".to_string(),
            "x4".to_string(),
            "x5".to_string(),
            "x6".to_string(),
            "x7".to_string(),
        ];
        let env = PassEnv {
            ptr_size: 64,
            sp_name: "sp",
            fp_name: "x29",
            ret_reg_name: "x0",
            function_names: &function_names,
            strings: &HashMap::new(),
            symbols: &HashMap::new(),
            callee_resolution: None,
            arg_regs: &arg_regs,
            param_register_aliases: &param_register_aliases,
            caller_saved_regs: &caller_saved_regs,
            type_hints: &type_hints,
            type_oracle: None,
        };

        let blocks = vec![entry, call_block];
        let use_info = UseInfo::analyze(&blocks, &env);
        let stack_info = StackInfo::analyze(&blocks, &use_info, &env);

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(function_names));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.atoi".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: false,
            },
        )]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(param_register_aliases));
        ctx.inputs.type_hints = Box::leak(Box::new(type_hints));
        ctx.state.analysis_ctx.use_info = use_info;
        ctx.state.analysis_ctx.stack_info = stack_info;

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:1000025d8", 0, 8),
                },
                0x100001368,
                6,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(args.len(), 1);
        assert!(
            matches!(
                &args[0],
                CExpr::Subscript { base, index }
                    if **base == CExpr::Var("argv".to_string()) && **index == CExpr::IntLit(1)
            ),
            "expected exact live 0x160 slot to still render argv[1], got: {:?}; semantic X8_10={:?}; semantic X0_5={:?}; stable_stack={:?}; stable_memory={:?}",
            args[0],
            ctx.state.analysis_ctx.use_info.semantic_values.get("X8_10"),
            ctx.state.analysis_ctx.use_info.semantic_values.get("X0_5"),
            ctx.state.analysis_ctx.use_info.stable_stack_values,
            ctx.state.analysis_ctx.use_info.stable_memory_values
        );
    }

    #[test]
    fn observed_live_arm64_usage_printf_renders_string_literal_and_argv0() {
        let sp0 = make_var("SP", 0, 8);
        let sp1 = make_var("SP", 1, 8);
        let sp2 = make_var("SP", 2, 8);
        let fp_slot = make_var("tmp:7b80", 1, 8);
        let frame_base = make_var("tmp:11f80", 2, 8);
        let slot_178 = make_var("tmp:6500", 1, 8);
        let slot_argv = make_var("tmp:6500", 2, 8);
        let call_slot = make_var("tmp:6500", 4, 8);
        let call_frame = make_var("X8", 5, 8);
        let argv_addr = make_var("tmp:6500", 5, 8);
        let argv_root = make_var("X8", 6, 8);
        let argv_deref_ptr = make_var("tmp:6800", 2, 8);
        let argv0 = make_var("X8", 7, 8);
        let stack_arg_base = make_var("X9", 2, 8);
        let stack_arg_slot = make_var("tmp:6800", 3, 8);
        let fmt_page = make_var("X0", 3, 8);
        let fmt_final = make_var("X0", 4, 8);

        let entry = SSABlock {
            addr: 0x100001308,
            size: 48,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: sp1.clone(),
                    a: sp0,
                    b: make_var("const:ffffffffffffffe0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: fp_slot.clone(),
                    a: sp1.clone(),
                    b: make_var("const:10", 0, 8),
                },
                SSAOp::IntSub {
                    dst: sp2.clone(),
                    a: sp1.clone(),
                    b: make_var("const:550", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: frame_base.clone(),
                    a: sp2.clone(),
                    b: make_var("const:3e0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: slot_178.clone(),
                    a: sp2.clone(),
                    b: make_var("const:178", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: slot_178,
                    val: frame_base.clone(),
                },
                SSAOp::IntAdd {
                    dst: slot_argv,
                    a: frame_base,
                    b: make_var("const:160", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: make_var("tmp:6500", 2, 8),
                    val: make_var("X1", 0, 8),
                },
            ],
        };

        let call_block = SSABlock {
            addr: 0x10000133c,
            size: 44,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: call_slot.clone(),
                    a: sp2.clone(),
                    b: make_var("const:178", 0, 8),
                },
                SSAOp::Load {
                    dst: call_frame.clone(),
                    space: "ram".to_string(),
                    addr: call_slot,
                },
                SSAOp::IntAdd {
                    dst: argv_addr.clone(),
                    a: call_frame,
                    b: make_var("const:160", 0, 8),
                },
                SSAOp::Load {
                    dst: argv_root.clone(),
                    space: "ram".to_string(),
                    addr: argv_addr,
                },
                SSAOp::Copy {
                    dst: argv_deref_ptr.clone(),
                    src: argv_root,
                },
                SSAOp::Load {
                    dst: argv0.clone(),
                    space: "ram".to_string(),
                    addr: argv_deref_ptr,
                },
                SSAOp::Copy {
                    dst: stack_arg_base.clone(),
                    src: sp2,
                },
                SSAOp::Copy {
                    dst: stack_arg_slot.clone(),
                    src: stack_arg_base,
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: stack_arg_slot,
                    val: argv0,
                },
                SSAOp::Copy {
                    dst: fmt_page,
                    src: make_var("const:100002000", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("tmp:11e80", 5, 8),
                    src: make_var("const:638", 0, 8),
                },
                SSAOp::IntCarry {
                    dst: make_var("TMPCY", 6, 1),
                    a: make_var("const:100002000", 0, 8),
                    b: make_var("const:638", 0, 8),
                },
                SSAOp::IntSCarry {
                    dst: make_var("TMPOV", 6, 1),
                    a: make_var("const:100002000", 0, 8),
                    b: make_var("const:638", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: make_var("tmp:11f80", 5, 8),
                    a: make_var("const:100002000", 0, 8),
                    b: make_var("const:638", 0, 8),
                },
                SSAOp::IntSLess {
                    dst: make_var("TMPNG", 6, 1),
                    a: make_var("const:100002638", 0, 8),
                    b: make_var("const:0", 0, 8),
                },
                SSAOp::IntEqual {
                    dst: make_var("TMPZR", 6, 1),
                    a: make_var("const:100002638", 0, 8),
                    b: make_var("const:0", 0, 8),
                },
                SSAOp::Copy {
                    dst: fmt_final.clone(),
                    src: make_var("const:100002638", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: make_var("X30", 3, 8),
                    a: make_var("const:100001358", 0, 8),
                    b: make_var("const:4", 0, 8),
                },
                SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
            ],
        };

        let function_names = HashMap::from([(0x10000259c, "sym.imp.printf".to_string())]);
        let strings =
            HashMap::from([(0x100002638, "Usage: %s <test_num> [args...]\\n".to_string())]);
        let _symbols: HashMap<u64, String> = HashMap::new();
        let param_register_aliases = HashMap::from([
            ("x0".to_string(), "argc".to_string()),
            ("x1".to_string(), "argv".to_string()),
            ("x2".to_string(), "envp".to_string()),
        ]);
        let type_hints = HashMap::from([
            ("argc".to_string(), CType::Int(32)),
            ("argv".to_string(), CType::ptr(CType::ptr(CType::Int(8)))),
            ("envp".to_string(), CType::ptr(CType::ptr(CType::Int(8)))),
        ]);
        let blocks = vec![entry, call_block];

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(function_names));
        ctx.inputs.strings = Box::leak(Box::new(strings));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.printf".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            },
        )]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(param_register_aliases));
        ctx.inputs.type_hints = Box::leak(Box::new(type_hints));
        ctx.analyze_blocks(&blocks);

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
                0x10000133c,
                18,
            )
            .expect("call should emit statement");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected call expression");
        };
        assert_eq!(
            args.len(),
            2,
            "expected printf format + argv[0], got {args:?}"
        );
        assert_eq!(
            args[0],
            CExpr::StringLit("Usage: %s <test_num> [args...]\\n".to_string()),
            "expected exact usage string literal, got {:?}",
            args[0]
        );
        assert!(
            matches!(
                &args[1],
                CExpr::Subscript { base, index }
                    if **base == CExpr::Var("argv".to_string()) && **index == CExpr::IntLit(0)
            ),
            "expected argv[0] for variadic printf stack arg, got {:?}",
            args[1]
        );
        assert!(
            !matches!(&args[0], CExpr::UIntLit(_))
                && !matches!(&args[1], CExpr::AddrOf(_))
                && !expr_contains_var(&args[1], "stack"),
            "printf imported args should not regress to raw literal or stack placeholders, got {:?}",
            args
        );

        let folded_stmts = ctx.fold_block(&blocks[1], blocks[1].addr);
        let folded_call_args = folded_stmts.iter().find_map(|stmt| {
            let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
                return None;
            };
            Some(args)
        });
        let Some(folded_call_args) = folded_call_args else {
            panic!("expected folded printf call statement, got {folded_stmts:?}");
        };
        assert_eq!(
            folded_call_args.first(),
            Some(&CExpr::StringLit(
                "Usage: %s <test_num> [args...]\\n".to_string()
            )),
            "expected folded printf format string literal, got {folded_stmts:?}"
        );
        assert!(
            matches!(
                folded_call_args.get(1),
                Some(CExpr::Subscript { base, index })
                    if **base == CExpr::Var("argv".to_string()) && **index == CExpr::IntLit(0)
            ),
            "expected folded printf argv[0] argument, got {folded_stmts:?}"
        );
        assert!(
            !folded_call_args.iter().any(|arg| match arg {
                CExpr::UIntLit(_) => true,
                CExpr::AddrOf(inner) => expr_contains_var(inner, "stack"),
                other => expr_contains_var(other, "stack"),
            }),
            "folded printf args should stay semantic and literalized, got {folded_stmts:?}"
        );
    }

    #[test]
    fn observed_live_arm64_boolxor_return_keeps_xor_shape() {
        let block = SSABlock {
            addr: 0x1000009c8,
            size: 48,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntSub {
                    dst: make_var("SP", 1, 8),
                    a: make_var("SP", 0, 8),
                    b: make_var("const:10", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: make_var("tmp:6400", 1, 8),
                    a: make_var("SP", 1, 8),
                    b: make_var("const:c", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: make_var("tmp:6400", 1, 8),
                    val: make_var("W0", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: make_var("tmp:6400", 2, 8),
                    a: make_var("SP", 1, 8),
                    b: make_var("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: make_var("tmp:6400", 2, 8),
                    val: make_var("W1", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: make_var("tmp:6400", 3, 8),
                    a: make_var("SP", 1, 8),
                    b: make_var("const:c", 0, 8),
                },
                SSAOp::Load {
                    dst: make_var("tmp:24c00", 1, 4),
                    space: "ram".to_string(),
                    addr: make_var("tmp:6400", 3, 8),
                },
                SSAOp::IntLessEqual {
                    dst: make_var("TMPCY", 1, 1),
                    a: make_var("const:0", 0, 4),
                    b: make_var("W8", 0, 4),
                },
                SSAOp::IntSBorrow {
                    dst: make_var("TMPOV", 1, 1),
                    a: make_var("W8", 0, 4),
                    b: make_var("const:0", 0, 4),
                },
                SSAOp::IntSub {
                    dst: make_var("tmp:3de80", 1, 4),
                    a: make_var("W8", 0, 4),
                    b: make_var("const:0", 0, 4),
                },
                SSAOp::IntSLess {
                    dst: make_var("TMPNG", 1, 1),
                    a: make_var("tmp:3de80", 1, 4),
                    b: make_var("const:0", 0, 4),
                },
                SSAOp::IntEqual {
                    dst: make_var("TMPZR", 1, 1),
                    a: make_var("tmp:3de80", 1, 4),
                    b: make_var("const:0", 0, 4),
                },
                SSAOp::Copy {
                    dst: make_var("NG", 1, 1),
                    src: make_var("TMPNG", 1, 1),
                },
                SSAOp::Copy {
                    dst: make_var("ZR", 1, 1),
                    src: make_var("TMPZR", 1, 1),
                },
                SSAOp::Copy {
                    dst: make_var("OV", 1, 1),
                    src: make_var("TMPOV", 1, 1),
                },
                SSAOp::BoolNot {
                    dst: make_var("tmp:2b80", 1, 1),
                    src: make_var("ZR", 1, 1),
                },
                SSAOp::IntEqual {
                    dst: make_var("tmp:2c00", 1, 1),
                    a: make_var("NG", 1, 1),
                    b: make_var("OV", 1, 1),
                },
                SSAOp::BoolAnd {
                    dst: make_var("tmp:2d00", 1, 1),
                    a: make_var("tmp:2b80", 1, 1),
                    b: make_var("tmp:2c00", 1, 1),
                },
                SSAOp::IntAdd {
                    dst: make_var("tmp:6400", 4, 8),
                    a: make_var("SP", 1, 8),
                    b: make_var("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: make_var("tmp:24c00", 2, 4),
                    space: "ram".to_string(),
                    addr: make_var("tmp:6400", 4, 8),
                },
                SSAOp::IntLessEqual {
                    dst: make_var("TMPCY", 2, 1),
                    a: make_var("const:0", 0, 4),
                    b: make_var("W9", 0, 4),
                },
                SSAOp::IntSBorrow {
                    dst: make_var("TMPOV", 2, 1),
                    a: make_var("W9", 0, 4),
                    b: make_var("const:0", 0, 4),
                },
                SSAOp::IntSub {
                    dst: make_var("tmp:3de80", 2, 4),
                    a: make_var("W9", 0, 4),
                    b: make_var("const:0", 0, 4),
                },
                SSAOp::IntSLess {
                    dst: make_var("TMPNG", 2, 1),
                    a: make_var("tmp:3de80", 2, 4),
                    b: make_var("const:0", 0, 4),
                },
                SSAOp::IntEqual {
                    dst: make_var("TMPZR", 2, 1),
                    a: make_var("tmp:3de80", 2, 4),
                    b: make_var("const:0", 0, 4),
                },
                SSAOp::Copy {
                    dst: make_var("NG", 2, 1),
                    src: make_var("TMPNG", 2, 1),
                },
                SSAOp::Copy {
                    dst: make_var("ZR", 2, 1),
                    src: make_var("TMPZR", 2, 1),
                },
                SSAOp::Copy {
                    dst: make_var("OV", 2, 1),
                    src: make_var("TMPOV", 2, 1),
                },
                SSAOp::BoolNot {
                    dst: make_var("tmp:2b80", 2, 1),
                    src: make_var("ZR", 2, 1),
                },
                SSAOp::IntEqual {
                    dst: make_var("tmp:2c00", 2, 1),
                    a: make_var("NG", 2, 1),
                    b: make_var("OV", 2, 1),
                },
                SSAOp::BoolAnd {
                    dst: make_var("tmp:2d00", 2, 1),
                    a: make_var("tmp:2b80", 2, 1),
                    b: make_var("tmp:2c00", 2, 1),
                },
                SSAOp::IntXor {
                    dst: make_var("tmp:20380", 1, 4),
                    a: make_var("W8", 0, 4),
                    b: make_var("W9", 0, 4),
                },
                SSAOp::IntZExt {
                    dst: make_var("X0", 1, 8),
                    src: make_var("tmp:20380", 1, 4),
                },
                SSAOp::IntAdd {
                    dst: make_var("tmp:11f80", 1, 8),
                    a: make_var("SP", 1, 8),
                    b: make_var("const:10", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("SP", 2, 8),
                    src: make_var("tmp:11f80", 1, 8),
                },
                SSAOp::Return {
                    target: make_var("X30", 0, 8),
                },
            ],
        };

        let mut ctx = make_aarch64_ctx();
        ctx.analyze_block(&block);
        ctx.state.return_blocks.insert(block.addr);
        assert!(
            ctx.state.return_stack_slots.is_empty(),
            "unexpected return stack slots for register-return xor case: {:?}",
            ctx.state.return_stack_slots
        );

        let stmts = ctx.fold_block(&block, block.addr);
        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("expected return statement, got {stmts:?}");
        };
        let (root, raw, semanticized) = ctx.debug_return_expr_stages(&make_var("tmp:20380", 1, 4));
        let def = ctx.lookup_definition("tmp:20380_1");
        let pred = ctx.lookup_predicate_expr("tmp:20380_1");
        assert!(
            expr_contains_binary_op(expr, BinaryOp::BitXor),
            "expected XOR-shaped return, got {expr:?}; def={def:?} pred={pred:?} root={root:?} raw={raw:?} semanticized={semanticized:?}"
        );
        assert!(
            !matches!(expr, CExpr::IntLit(10) | CExpr::UIntLit(10)),
            "epilogue stack adjustment leaked into return value: {expr:?}"
        );
    }

    #[test]
    fn exact_symbol_store_prefers_exact_global_symbol_over_base_symbol_offset() {
        let block = make_block(vec![SSAOp::Store {
            space: "ram".to_string(),
            addr: make_var("const:100008008", 0, 8),
            val: make_var("W8", 0, 4),
        }]);

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.symbols = Box::leak(Box::new(HashMap::from([
            (0x100008000, "sym._global_limit".to_string()),
            (0x100008004, "sym._global_counter".to_string()),
            (0x100008008, "sym._global_tail".to_string()),
        ])));
        ctx.analyze_block(&block);

        let stmts = ctx.fold_block(&block, block.addr);
        let Some(CStmt::Expr(CExpr::Binary { left, .. })) = stmts.first() else {
            panic!("expected store assignment, got {stmts:?}");
        };
        assert_eq!(
            left.as_ref(),
            &CExpr::Var("sym._global_tail".to_string()),
            "expected exact symbol store target, got {left:?}"
        );
    }

    #[test]
    fn exact_symbol_store_prefers_exact_global_symbol_over_constant_indexed_base() {
        let block = make_block(vec![SSAOp::Store {
            space: "ram".to_string(),
            addr: make_var("tmp:storeptr", 1, 8),
            val: make_var("W8", 0, 4),
        }]);

        let mut ctx = make_aarch64_ctx();
        ctx.inputs.symbols = Box::leak(Box::new(HashMap::from([
            (0x100008000, "sym._global_limit".to_string()),
            (0x100008004, "sym._global_counter".to_string()),
            (0x100008008, "sym._global_tail".to_string()),
        ])));
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            "tmp:storeptr_1".to_string(),
            crate::analysis::SemanticValue::Address(crate::analysis::NormalizedAddr {
                base: crate::analysis::BaseRef::Raw(CExpr::Var("sym._global_limit".to_string())),
                index: Some(crate::analysis::ValueRef::from(make_var("const:1", 0, 8))),
                scale_bytes: 8,
                offset_bytes: 0,
            }),
        );

        let stmts = ctx.fold_block(&block, block.addr);
        let Some(CStmt::Expr(CExpr::Binary { left, .. })) = stmts.first() else {
            panic!("expected store assignment, got {stmts:?}");
        };
        assert_eq!(
            left.as_ref(),
            &CExpr::Var("sym._global_tail".to_string()),
            "expected exact symbol store target from constant indexed base, got {left:?}"
        );
    }

    #[test]
    fn observed_live_arm64_check_secret_exact_shape_returns_zero_and_one() {
        use r2il::R2ILBlock;
        use r2ssa::SSAFunction;

        let mut b0 = R2ILBlock::new(0x100000598, 4);
        b0.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1000005c0, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut b_else = R2ILBlock::new(0x10000059c, 4);
        b_else.push(R2ILOp::Branch {
            target: Varnode::constant(0x1000005c8, 8),
        });
        let mut b_then = R2ILBlock::new(0x1000005c0, 4);
        b_then.push(R2ILOp::Branch {
            target: Varnode::constant(0x1000005c8, 8),
        });
        let mut b_exit = R2ILBlock::new(0x1000005c8, 4);
        b_exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let blocks = vec![b0, b_else, b_then, b_exit];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        func = func.with_name("sym._check_secret");

        func.get_block_mut(0x100000598).expect("entry").ops = vec![
            SSAOp::IntSub {
                dst: make_var("SP", 1, 8),
                a: make_var("SP", 0, 8),
                b: make_var("const:10", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 1, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 1, 8),
                val: make_var("W0", 0, 4),
            },
            SSAOp::Copy {
                dst: make_var("tmp:3e480", 1, 4),
                src: make_var("const:dead", 0, 4),
            },
            SSAOp::IntSub {
                dst: make_var("tmp:3e580", 1, 4),
                a: make_var("W0", 0, 4),
                b: make_var("tmp:3e480", 1, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("TMPZR", 1, 1),
                a: make_var("tmp:3e580", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:a00", 1, 1),
                src: make_var("TMPZR", 1, 1),
            },
            SSAOp::CBranch {
                target: make_var("ram:1000005c0", 0, 8),
                cond: make_var("tmp:a00", 1, 1),
            },
        ];
        func.get_block_mut(0x1000005c0).expect("then").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 6, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 6, 8),
                val: make_var("const:0", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1000005c8", 0, 8),
            },
        ];
        func.get_block_mut(0x10000059c).expect("else").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 5, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 5, 8),
                val: make_var("const:1", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1000005c8", 0, 8),
            },
        ];
        func.get_block_mut(0x1000005c8).expect("exit").ops = vec![SSAOp::Return {
            target: make_var("X30", 0, 8),
        }];

        let mut decompiler = crate::Decompiler::new(crate::DecompilerConfig::aarch64());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(crate::CType::Int(64)),
                vec![("arg1", Some(crate::CType::UInt(64)))],
            )),
            external_stack_vars: HashMap::from([(
                12,
                stack_var_spec("var_ch", Some(crate::CType::Int(32)), Some("sp")),
            )]),
            ..FunctionTypeFacts::default()
        });

        let output = decompiler.decompile(&func);
        assert!(
            output.contains("return 0;") && output.contains("return 1;"),
            "expected concrete returns for exact observed shape, got:\n{output}"
        );
        assert!(
            !output.contains("&arg1"),
            "exact observed shape must not degrade to &arg1, got:\n{output}"
        );
    }

    #[test]
    fn observed_live_arm64_main_usage_path_returns_one_not_argc() {
        use r2il::R2ILBlock;
        use r2ssa::SSAFunction;

        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1020, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut usage = R2ILBlock::new(0x1004, 4);
        usage.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut body = R2ILBlock::new(0x1020, 4);
        body.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut exit = R2ILBlock::new(0x1010, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let blocks = vec![entry, usage, body, exit];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        func = func.with_name("sym._main");

        func.get_block_mut(0x1000).expect("entry").ops = vec![SSAOp::CBranch {
            target: make_var("ram:1020", 0, 8),
            cond: make_var("tmp:a00", 1, 1),
        }];
        func.get_block_mut(0x1004).expect("usage").ops = vec![
            SSAOp::Copy {
                dst: make_var("X0", 1, 8),
                src: make_var("const:100002638", 0, 8),
            },
            SSAOp::Call {
                target: make_var("const:10000259c", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("X8", 1, 8),
                src: make_var("const:1", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:retcopy", 1, 4),
                src: make_var("W8", 0, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 1, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 1, 8),
                val: make_var("tmp:retcopy", 1, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1010", 0, 8),
            },
        ];
        func.get_block_mut(0x1020).expect("body").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 2, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 2, 8),
                val: make_var("const:0", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:1010", 0, 8),
            },
        ];
        func.get_block_mut(0x1010).expect("exit").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:6400", 3, 8),
                a: make_var("SP", 1, 8),
                b: make_var("const:c", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:24c00", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:6400", 3, 8),
            },
            SSAOp::IntZExt {
                dst: make_var("X0", 2, 8),
                src: make_var("tmp:24c00", 1, 4),
            },
            SSAOp::Return {
                target: make_var("X30", 0, 8),
            },
        ];

        let mut decompiler = crate::Decompiler::new(crate::DecompilerConfig::aarch64());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(crate::CType::Int(64)),
                vec![
                    ("argc", Some(crate::CType::Int(32))),
                    (
                        "argv",
                        Some(crate::CType::Pointer(Box::new(crate::CType::Pointer(
                            Box::new(crate::CType::Int(8)),
                        )))),
                    ),
                ],
            )),
            external_stack_vars: HashMap::from([(
                12,
                stack_var_spec("var_ch", Some(crate::CType::Int(32)), Some("sp")),
            )]),
            ..FunctionTypeFacts::default()
        });
        decompiler.set_function_names(HashMap::from([(0x10000259c, "sym.imp.printf".to_string())]));
        let known_printf_sigs = HashMap::from([(
            "sym.imp.printf".to_string(),
            r2types::FunctionType::from(FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            }),
        )]);
        decompiler.set_known_function_signatures(known_printf_sigs);
        decompiler.set_strings(HashMap::from([(
            0x100002638,
            "Usage: %s <test_num> [args...]\\n".to_string(),
        )]));

        let output = decompiler.decompile(&func);
        assert!(
            output.contains("return 1;"),
            "expected usage path to keep constant return, got:\n{output}"
        );
        assert!(
            !output.contains("return argc;"),
            "usage path must not regress to returning argc, got:\n{output}"
        );
    }

    #[test]
    fn folded_arm64_printf_keeps_preserved_inputs_and_helper_result_semantic() {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x1000005d4, "sym._unlock".to_string()),
            (0x10000259c, "sym.imp.printf".to_string()),
        ])));
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x1000027a0,
            "unlock(%d, %d, %d) = %d\\n".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym._unlock".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::Int(32), CType::Int(32), CType::Int(32)],
                    variadic: false,
                },
            ),
            (
                "sym.imp.printf".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: true,
                },
            ),
        ]));

        let sp = make_var("SP", 2, 8);
        let x0_1 = make_var("X0", 1, 8);
        let x1_1 = make_var("X1", 1, 8);
        let x2_1 = make_var("X2", 1, 8);
        let home_a = make_var("tmp:home", 1, 8);
        let home_b = make_var("tmp:home", 2, 8);
        let home_c = make_var("tmp:home", 3, 8);
        let x0_ret = make_var("X0", 2, 8);
        let x11_1 = make_var("X11", 1, 8);
        let x10_1 = make_var("X10", 1, 8);
        let x8_1 = make_var("X8", 1, 8);

        let block = SSABlock {
            addr: 0x10000141c,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Copy {
                    dst: x0_1.clone(),
                    src: make_var("const:1", 0, 8),
                },
                SSAOp::Copy {
                    dst: x1_1.clone(),
                    src: make_var("const:2", 0, 8),
                },
                SSAOp::Copy {
                    dst: x2_1.clone(),
                    src: make_var("const:3", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: home_a.clone(),
                    a: sp.clone(),
                    b: make_var("const:150", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: home_a.clone(),
                    val: x0_1.clone(),
                },
                SSAOp::IntAdd {
                    dst: home_b.clone(),
                    a: sp.clone(),
                    b: make_var("const:158", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: home_b.clone(),
                    val: x1_1.clone(),
                },
                SSAOp::IntAdd {
                    dst: home_c.clone(),
                    a: sp.clone(),
                    b: make_var("const:160", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: home_c.clone(),
                    val: x2_1.clone(),
                },
                SSAOp::Call {
                    target: make_var("const:1000005d4", 0, 8),
                },
                SSAOp::CallDefine {
                    dst: x0_ret.clone(),
                },
                SSAOp::Load {
                    dst: x11_1.clone(),
                    space: "ram".to_string(),
                    addr: home_a,
                },
                SSAOp::Load {
                    dst: x10_1.clone(),
                    space: "ram".to_string(),
                    addr: home_b,
                },
                SSAOp::Load {
                    dst: x8_1.clone(),
                    space: "ram".to_string(),
                    addr: home_c,
                },
                SSAOp::Copy {
                    dst: make_var("X0", 3, 8),
                    src: make_var("const:1000027a0", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("X1", 2, 8),
                    src: x11_1,
                },
                SSAOp::Copy {
                    dst: make_var("X2", 2, 8),
                    src: x10_1,
                },
                SSAOp::Copy {
                    dst: make_var("X3", 1, 8),
                    src: x8_1,
                },
                SSAOp::Copy {
                    dst: make_var("X4", 1, 8),
                    src: x0_ret,
                },
                SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
            ],
        };

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let Some(CExpr::Call { func, args }) =
            ctx.state.analysis_ctx.use_info.definitions.get("X0_2")
        else {
            panic!(
                "expected helper return register to bind to a helper call expression, got {:?}",
                ctx.state.analysis_ctx.use_info.definitions.get("X0_2")
            );
        };
        assert_eq!(**func, CExpr::Var("sym._unlock".to_string()));
        assert!(
            args == &vec![CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]
                || args
                    == &vec![
                        CExpr::IntLit(1),
                        CExpr::IntLit(2),
                        CExpr::IntLit(3),
                        CExpr::IntLit(1),
                        CExpr::IntLit(2),
                        CExpr::IntLit(3),
                    ],
            "expected helper return register to keep the helper call inputs, got {args:?}"
        );
        let printf_call_args = ctx
            .state
            .analysis_ctx
            .use_info
            .call_args
            .get(&(block.addr, block.ops.len() - 1))
            .expect("printf call args");
        assert!(
            matches!(
                printf_call_args.last(),
                Some(crate::analysis::CallArgBinding {
                    arg: crate::analysis::SemanticCallArg::FallbackExpr(CExpr::Call { func, args }),
                    role: crate::analysis::CallArgRole::Result,
                    ..
                }) if **func == CExpr::Var("sym._unlock".to_string())
                    && (args == &vec![CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]
                        || args
                            == &vec![
                                CExpr::IntLit(1),
                                CExpr::IntLit(2),
                                CExpr::IntLit(3),
                                CExpr::IntLit(1),
                                CExpr::IntLit(2),
                                CExpr::IntLit(3),
                            ])
            ),
            "expected printf call args to preserve the helper result expression, got {printf_call_args:?}"
        );
        let stmts = ctx.fold_block(&block, block.addr);
        assert_eq!(
            stmts.len(),
            1,
            "expected helper call to inline into the printf use, got {stmts:?}"
        );

        let CStmt::Expr(CExpr::Call { func, args }) = &stmts[0] else {
            panic!("expected folded printf call, got {stmts:?}");
        };
        assert_eq!(**func, CExpr::Var("sym.imp.printf".to_string()));
        assert_eq!(
            args.first(),
            Some(&CExpr::StringLit("unlock(%d, %d, %d) = %d\\n".to_string()))
        );
        assert_eq!(
            &args[1..4],
            &[CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]
        );
        let CExpr::Call {
            func: helper_func,
            args: helper_args,
        } = &args[4]
        else {
            panic!(
                "expected helper result call in final printf arg, got {:?}; full args={args:?}",
                args[4]
            );
        };
        assert_eq!(**helper_func, CExpr::Var("sym._unlock".to_string()));
        assert_eq!(
            helper_args,
            &vec![CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]
        );
        assert!(
            args.iter()
                .skip(1)
                .all(|arg| !expr_contains_transient_call_artifact(arg)),
            "later printf args should not regress to transient register or stack artifacts, got {args:?}"
        );
    }

    #[test]
    fn folded_arm64_printf_recovers_helper_result_without_calldefine() {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x1000005d4, "sym._unlock".to_string()),
            (0x10000259c, "sym.imp.printf".to_string()),
        ])));
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x1000027a0,
            "unlock(%d, %d, %d) = %d\\n".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym._unlock".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::Int(32), CType::Int(32), CType::Int(32)],
                    variadic: false,
                },
            ),
            (
                "sym.imp.printf".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: true,
                },
            ),
        ]));

        let sp = make_var("SP", 2, 8);
        let x0_1 = make_var("X0", 1, 8);
        let x1_1 = make_var("X1", 1, 8);
        let x2_1 = make_var("X2", 1, 8);
        let x0_12 = make_var("X0", 12, 8);
        let home_a = make_var("tmp:home", 1, 8);
        let home_b = make_var("tmp:home", 2, 8);
        let home_c = make_var("tmp:home", 3, 8);
        let x11_2 = make_var("X11", 2, 8);
        let x10_3 = make_var("X10", 3, 8);
        let x8_33 = make_var("X8", 33, 8);
        let x8_43 = make_var("X8", 43, 8);
        let printf_slot_b = make_var("tmp:printf_home", 2, 8);
        let printf_slot_c = make_var("tmp:printf_home", 3, 8);
        let printf_slot_ret = make_var("tmp:printf_home", 4, 8);

        let block = SSABlock {
            addr: 0x10000141c,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Copy {
                    dst: x0_1.clone(),
                    src: make_var("const:1", 0, 8),
                },
                SSAOp::Copy {
                    dst: x1_1.clone(),
                    src: make_var("const:2", 0, 8),
                },
                SSAOp::Copy {
                    dst: x2_1.clone(),
                    src: make_var("const:3", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: home_a.clone(),
                    a: sp.clone(),
                    b: make_var("const:150", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: home_a.clone(),
                    val: x0_1.clone(),
                },
                SSAOp::IntAdd {
                    dst: home_b.clone(),
                    a: sp.clone(),
                    b: make_var("const:158", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: home_b.clone(),
                    val: x1_1.clone(),
                },
                SSAOp::IntAdd {
                    dst: home_c.clone(),
                    a: sp.clone(),
                    b: make_var("const:160", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: home_c.clone(),
                    val: x2_1.clone(),
                },
                SSAOp::Copy {
                    dst: x0_12.clone(),
                    src: x0_1,
                },
                SSAOp::Call {
                    target: make_var("const:1000005d4", 0, 8),
                },
                SSAOp::Load {
                    dst: x11_2.clone(),
                    space: "ram".to_string(),
                    addr: home_a,
                },
                SSAOp::Load {
                    dst: x10_3.clone(),
                    space: "ram".to_string(),
                    addr: home_b,
                },
                SSAOp::Load {
                    dst: x8_33.clone(),
                    space: "ram".to_string(),
                    addr: home_c,
                },
                SSAOp::Copy {
                    dst: x8_43.clone(),
                    src: x0_12,
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: sp.clone(),
                    val: x11_2,
                },
                SSAOp::IntAdd {
                    dst: printf_slot_b.clone(),
                    a: sp.clone(),
                    b: make_var("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: printf_slot_b,
                    val: x10_3,
                },
                SSAOp::IntAdd {
                    dst: printf_slot_c.clone(),
                    a: sp.clone(),
                    b: make_var("const:10", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: printf_slot_c,
                    val: x8_33,
                },
                SSAOp::IntAdd {
                    dst: printf_slot_ret.clone(),
                    a: sp.clone(),
                    b: make_var("const:18", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: printf_slot_ret,
                    val: x8_43,
                },
                SSAOp::Copy {
                    dst: make_var("X0", 20, 8),
                    src: make_var("const:1000027a0", 0, 8),
                },
                SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
            ],
        };

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let printf_call_args = ctx
            .state
            .analysis_ctx
            .use_info
            .call_args
            .get(&(block.addr, block.ops.len() - 1))
            .expect("printf call args");
        assert!(
            matches!(
                printf_call_args.last(),
                Some(crate::analysis::CallArgBinding {
                    arg: crate::analysis::SemanticCallArg::FallbackExpr(CExpr::Call { func, args }),
                    role: crate::analysis::CallArgRole::Result,
                    ..
                }) if **func == CExpr::Var("sym._unlock".to_string())
                    && args == &vec![CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]
            ),
            "expected post-call X0 reuse to recover helper result, got {printf_call_args:?}"
        );

        let stmts = ctx.fold_block(&block, block.addr);
        let CStmt::Expr(CExpr::Call { args, .. }) = &stmts[0] else {
            panic!("expected folded printf call, got {stmts:?}");
        };
        let CExpr::Call {
            func: helper_func,
            args: helper_args,
        } = &args[4]
        else {
            panic!("expected helper result call in final printf arg, got {args:?}");
        };
        assert_eq!(
            &args[1..4],
            &[CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]
        );
        assert_eq!(**helper_func, CExpr::Var("sym._unlock".to_string()));
        assert_eq!(
            helper_args,
            &vec![CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]
        );
        assert!(
            args.iter()
                .skip(1)
                .all(|arg| !expr_contains_transient_call_artifact(arg)),
            "post-call helper recovery must keep preserved inputs clean, got {args:?}"
        );
    }

    #[test]
    fn aarch64_unused_helper_call_result_renders_as_side_effect_call() {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x1000005d4,
            "sym._unlock".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym._unlock".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Void)],
                variadic: false,
            },
        )]));

        let block = SSABlock {
            addr: 0x100001000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Copy {
                    dst: make_var("X0", 1, 8),
                    src: make_var("const:1234", 0, 8),
                },
                SSAOp::Call {
                    target: make_var("const:1000005d4", 0, 8),
                },
                SSAOp::CallDefine {
                    dst: make_var("X0", 2, 8),
                },
                SSAOp::Return {
                    target: make_var("const:0", 0, 8),
                },
            ],
        };

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let stmts = ctx.fold_block(&block, block.addr);
        assert!(
            matches!(
                stmts.first(),
                Some(CStmt::Expr(CExpr::Call { func, .. }))
                    if **func == CExpr::Var("sym._unlock".to_string())
            ),
            "unused helper result should render as a side-effect call, got {stmts:?}"
        );
        assert!(
            !stmts.iter().any(|stmt| matches!(
                stmt,
                CStmt::Expr(CExpr::Binary {
                    op: BinaryOp::Assign,
                    left,
                    right,
                }) if matches!(left.as_ref(), CExpr::Var(name) if name.eq_ignore_ascii_case("x0_2"))
                    && matches!(right.as_ref(), CExpr::Call { .. })
            )),
            "unused helper result must not materialize a transient assignment, got {stmts:?}"
        );
    }

    #[test]
    fn folded_arm64_printf_live_unlock_shape_recovers_result_slot_from_negative_local_loads() {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x1000005d4, "sym._unlock".to_string()),
            (0x10000259c, "sym.imp.printf".to_string()),
        ])));
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x10000266f,
            "unlock(%d, %d, %d) = %d\\n".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym._unlock".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::Int(32), CType::Int(32), CType::Int(32)],
                    variadic: false,
                },
            ),
            (
                "sym.imp.printf".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: true,
                },
            ),
        ]));
        ctx.set_external_stack_vars(HashMap::from([
            (
                -44,
                stack_var_spec("local_2c", Some(CType::Int(32)), Some("x29")),
            ),
            (
                -48,
                stack_var_spec("local_30", Some(CType::Int(32)), Some("x29")),
            ),
            (
                -52,
                stack_var_spec("local_34", Some(CType::Int(32)), Some("x29")),
            ),
        ]));

        let sp = make_var("SP", 2, 8);
        let fp = make_var("X29", 1, 8);
        let slot_a = make_var("tmp:6980", 18, 8);
        let slot_b = make_var("tmp:6980", 19, 8);
        let slot_c = make_var("tmp:6980", 20, 8);
        let local_a = make_var("tmp:24d00", 11, 4);
        let local_b = make_var("tmp:24d00", 12, 4);
        let local_c = make_var("tmp:24d00", 13, 4);
        let x0_12 = make_var("X0", 12, 8);
        let x1_1 = make_var("X1", 1, 8);
        let x2_1 = make_var("X2", 1, 8);
        let x11_2 = make_var("X11", 2, 8);
        let x10_3 = make_var("X10", 3, 8);
        let x8_33 = make_var("X8", 33, 8);
        let x8_34 = make_var("X8", 34, 8);
        let home0 = make_var("tmp:6800", 5, 8);
        let home1 = make_var("tmp:6500", 32, 8);
        let home2 = make_var("tmp:6500", 33, 8);
        let home3 = make_var("tmp:6500", 34, 8);

        let block = SSABlock {
            addr: 0x100001458,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: slot_a.clone(),
                    a: fp.clone(),
                    b: make_var("const:ffffffffffffffd4", 0, 8),
                },
                SSAOp::Load {
                    dst: local_a.clone(),
                    space: "ram".to_string(),
                    addr: slot_a,
                },
                SSAOp::IntZExt {
                    dst: x0_12.clone(),
                    src: local_a,
                },
                SSAOp::IntAdd {
                    dst: slot_b.clone(),
                    a: fp.clone(),
                    b: make_var("const:ffffffffffffffd0", 0, 8),
                },
                SSAOp::Load {
                    dst: local_b.clone(),
                    space: "ram".to_string(),
                    addr: slot_b,
                },
                SSAOp::IntZExt {
                    dst: x1_1.clone(),
                    src: local_b,
                },
                SSAOp::IntAdd {
                    dst: slot_c.clone(),
                    a: fp.clone(),
                    b: make_var("const:ffffffffffffffcc", 0, 8),
                },
                SSAOp::Load {
                    dst: local_c.clone(),
                    space: "ram".to_string(),
                    addr: slot_c,
                },
                SSAOp::IntZExt {
                    dst: x2_1.clone(),
                    src: local_c,
                },
                SSAOp::Call {
                    target: make_var("const:1000005d4", 0, 8),
                },
                SSAOp::Copy {
                    dst: x11_2.clone(),
                    src: x0_12.clone(),
                },
                SSAOp::Copy {
                    dst: x10_3.clone(),
                    src: x1_1,
                },
                SSAOp::Copy {
                    dst: x8_33.clone(),
                    src: x2_1,
                },
                SSAOp::Copy {
                    dst: home0.clone(),
                    src: sp.clone(),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: home0,
                    val: x11_2,
                },
                SSAOp::IntAdd {
                    dst: home1.clone(),
                    a: sp.clone(),
                    b: make_var("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: home1,
                    val: x10_3,
                },
                SSAOp::IntAdd {
                    dst: home2.clone(),
                    a: sp.clone(),
                    b: make_var("const:10", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: home2,
                    val: x8_33,
                },
                SSAOp::Copy {
                    dst: x8_34.clone(),
                    src: x0_12,
                },
                SSAOp::IntAdd {
                    dst: home3.clone(),
                    a: sp.clone(),
                    b: make_var("const:18", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: home3,
                    val: x8_34,
                },
                SSAOp::Copy {
                    dst: make_var("X0", 13, 8),
                    src: make_var("const:10000266f", 0, 8),
                },
                SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
            ],
        };

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let printf_call_args = ctx
            .state
            .analysis_ctx
            .use_info
            .call_args
            .get(&(block.addr, block.ops.len() - 1))
            .expect("printf call args");
        assert!(
            matches!(
                printf_call_args.last(),
                Some(crate::analysis::CallArgBinding {
                    arg: crate::analysis::SemanticCallArg::FallbackExpr(CExpr::Call { func, .. }),
                    role: crate::analysis::CallArgRole::Result,
                    ..
                }) if **func == CExpr::Var("sym._unlock".to_string())
            ),
            "expected live-shaped unlock printf to keep helper result in final slot, got {printf_call_args:?}"
        );

        let stmts = ctx.fold_block(&block, block.addr);
        let CStmt::Expr(CExpr::Call { args, .. }) = &stmts[0] else {
            panic!("expected folded printf call, got {stmts:?}");
        };
        assert!(
            matches!(&args[4], CExpr::Call { func, .. } if **func == CExpr::Var("sym._unlock".to_string())),
            "expected final printf arg to be helper result call, got {args:?}"
        );
        assert!(
            args.iter()
                .skip(1)
                .all(|arg| !expr_contains_transient_call_artifact(arg)),
            "live-shaped unlock printf args should not regress to transient artifacts, got {args:?}"
        );
    }

    #[test]
    fn folded_arm64_printf_live_unlock_shape_with_prior_atoi_preserves_uncertified_siblings() {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x1000005d4, "sym._unlock".to_string()),
            (0x10000259c, "sym.imp.printf".to_string()),
            (0x1000025d8, "sym.imp.atoi".to_string()),
        ])));
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x10000266f,
            "unlock(%d, %d, %d) = %d\\n".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym._unlock".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::Int(32), CType::Int(32), CType::Int(32)],
                    variadic: false,
                },
            ),
            (
                "sym.imp.printf".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: true,
                },
            ),
            (
                "sym.imp.atoi".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: false,
                },
            ),
        ]));
        ctx.set_external_stack_vars(HashMap::from([
            (
                -44,
                stack_var_spec("local_2c", Some(CType::Int(32)), Some("x29")),
            ),
            (
                -48,
                stack_var_spec("local_30", Some(CType::Int(32)), Some("x29")),
            ),
            (
                -52,
                stack_var_spec("local_34", Some(CType::Int(32)), Some("x29")),
            ),
        ]));
        ctx.inputs.visible_bindings = Box::leak(Box::new(vec![
            visible_stack_binding("local_2c", Some(CType::Int(32)), -44),
            visible_stack_binding("local_30", Some(CType::Int(32)), -48),
            visible_stack_binding("local_34", Some(CType::Int(32)), -52),
        ]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([
            ("x0".to_string(), "argc".to_string()),
            ("x1".to_string(), "argv".to_string()),
            ("x2".to_string(), "envp".to_string()),
        ])));
        ctx.inputs.type_hints = Box::leak(Box::new(HashMap::from([
            ("argc".to_string(), CType::Int(32)),
            ("argv".to_string(), CType::ptr(CType::ptr(CType::Int(8)))),
            ("envp".to_string(), CType::ptr(CType::ptr(CType::Int(8)))),
        ])));

        let sp = make_var("SP", 2, 8);
        let fp = make_var("X29", 1, 8);
        let argv = make_var("X1", 0, 8);

        let slot_a_seed = make_var("tmp:6980", 11, 8);
        let slot_b_seed = make_var("tmp:6980", 12, 8);
        let slot_c_seed = make_var("tmp:6980", 13, 8);
        let argv_4_addr = make_var("tmp:6500", 20, 8);
        let atoi_arg = make_var("X0", 11, 8);
        let atoi_tmp = make_var("tmp:3a680", 7, 4);
        let helper_home_a = make_var("tmp:6500", 26, 8);
        let helper_home_b = make_var("tmp:6500", 27, 8);
        let helper_home_c = make_var("tmp:6500", 28, 8);
        let helper_arg_a = make_var("X8", 30, 8);
        let helper_arg_b = make_var("X8", 31, 8);
        let helper_arg_c = make_var("X8", 32, 8);
        let helper_x0 = make_var("X0", 12, 8);
        let helper_x1 = make_var("X1", 1, 8);
        let helper_x2 = make_var("X2", 1, 8);
        let printf_home0 = make_var("tmp:6800", 5, 8);
        let printf_home1 = make_var("tmp:6500", 32, 8);
        let printf_home2 = make_var("tmp:6500", 33, 8);
        let printf_home_ret = make_var("tmp:6500", 34, 8);
        let post_a = make_var("X11", 2, 8);
        let post_b = make_var("X10", 3, 8);
        let post_c = make_var("X8", 33, 8);
        let post_ret = make_var("X8", 34, 8);
        let printf_base = make_var("X9", 4, 8);

        let block = SSABlock {
            addr: 0x10000141c,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: slot_a_seed.clone(),
                    a: fp.clone(),
                    b: make_var("const:ffffffffffffffd4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: slot_a_seed.clone(),
                    val: make_var("const:1", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: slot_b_seed.clone(),
                    a: fp.clone(),
                    b: make_var("const:ffffffffffffffd0", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: slot_b_seed.clone(),
                    val: make_var("const:2", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: argv_4_addr.clone(),
                    a: argv.clone(),
                    b: make_var("const:20", 0, 8),
                },
                SSAOp::Load {
                    dst: atoi_arg.clone(),
                    space: "ram".to_string(),
                    addr: argv_4_addr,
                },
                SSAOp::Call {
                    target: make_var("const:1000025d8", 0, 8),
                },
                SSAOp::Copy {
                    dst: atoi_tmp.clone(),
                    src: make_var("W0", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: slot_c_seed.clone(),
                    a: fp.clone(),
                    b: make_var("const:ffffffffffffffcc", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: slot_c_seed.clone(),
                    val: atoi_tmp,
                },
                SSAOp::Load {
                    dst: make_var("tmp:24d00", 8, 4),
                    space: "ram".to_string(),
                    addr: slot_a_seed.clone(),
                },
                SSAOp::IntZExt {
                    dst: helper_arg_a.clone(),
                    src: make_var("tmp:24d00", 8, 4),
                },
                SSAOp::IntAdd {
                    dst: helper_home_a.clone(),
                    a: sp.clone(),
                    b: make_var("const:150", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: helper_home_a.clone(),
                    val: helper_arg_a,
                },
                SSAOp::Load {
                    dst: make_var("tmp:24d00", 9, 4),
                    space: "ram".to_string(),
                    addr: slot_b_seed.clone(),
                },
                SSAOp::IntZExt {
                    dst: helper_arg_b.clone(),
                    src: make_var("tmp:24d00", 9, 4),
                },
                SSAOp::IntAdd {
                    dst: helper_home_b.clone(),
                    a: sp.clone(),
                    b: make_var("const:158", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: helper_home_b.clone(),
                    val: helper_arg_b,
                },
                SSAOp::Load {
                    dst: make_var("tmp:24d00", 10, 4),
                    space: "ram".to_string(),
                    addr: slot_c_seed.clone(),
                },
                SSAOp::IntZExt {
                    dst: helper_arg_c.clone(),
                    src: make_var("tmp:24d00", 10, 4),
                },
                SSAOp::IntAdd {
                    dst: helper_home_c.clone(),
                    a: sp.clone(),
                    b: make_var("const:160", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: helper_home_c.clone(),
                    val: helper_arg_c,
                },
                SSAOp::Load {
                    dst: make_var("tmp:24d00", 11, 4),
                    space: "ram".to_string(),
                    addr: slot_a_seed,
                },
                SSAOp::IntZExt {
                    dst: helper_x0.clone(),
                    src: make_var("tmp:24d00", 11, 4),
                },
                SSAOp::Load {
                    dst: make_var("tmp:24d00", 12, 4),
                    space: "ram".to_string(),
                    addr: slot_b_seed,
                },
                SSAOp::IntZExt {
                    dst: helper_x1.clone(),
                    src: make_var("tmp:24d00", 12, 4),
                },
                SSAOp::Load {
                    dst: make_var("tmp:24d00", 13, 4),
                    space: "ram".to_string(),
                    addr: slot_c_seed,
                },
                SSAOp::IntZExt {
                    dst: helper_x2.clone(),
                    src: make_var("tmp:24d00", 13, 4),
                },
                SSAOp::Call {
                    target: make_var("const:1000005d4", 0, 8),
                },
                SSAOp::Load {
                    dst: post_a.clone(),
                    space: "ram".to_string(),
                    addr: helper_home_a,
                },
                SSAOp::Load {
                    dst: post_b.clone(),
                    space: "ram".to_string(),
                    addr: helper_home_b,
                },
                SSAOp::Load {
                    dst: post_c.clone(),
                    space: "ram".to_string(),
                    addr: helper_home_c,
                },
                SSAOp::Copy {
                    dst: printf_base.clone(),
                    src: sp.clone(),
                },
                SSAOp::Copy {
                    dst: printf_home0.clone(),
                    src: printf_base.clone(),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: printf_home0,
                    val: post_a,
                },
                SSAOp::IntAdd {
                    dst: printf_home1.clone(),
                    a: printf_base.clone(),
                    b: make_var("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: printf_home1,
                    val: post_b,
                },
                SSAOp::IntAdd {
                    dst: printf_home2.clone(),
                    a: printf_base.clone(),
                    b: make_var("const:10", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: printf_home2,
                    val: post_c,
                },
                SSAOp::Copy {
                    dst: post_ret.clone(),
                    src: helper_x0,
                },
                SSAOp::IntAdd {
                    dst: printf_home_ret.clone(),
                    a: printf_base,
                    b: make_var("const:18", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: printf_home_ret,
                    val: post_ret,
                },
                SSAOp::Copy {
                    dst: make_var("X0", 14, 8),
                    src: make_var("const:10000266f", 0, 8),
                },
                SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
            ],
        };

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let printf_call_args = ctx
            .state
            .analysis_ctx
            .use_info
            .call_args
            .get(&(block.addr, block.ops.len() - 1))
            .expect("printf call args");
        assert!(
            matches!(
                printf_call_args.last(),
                Some(crate::analysis::CallArgBinding {
                    arg: crate::analysis::SemanticCallArg::FallbackExpr(CExpr::Call { func, .. }),
                    role: crate::analysis::CallArgRole::Result,
                    ..
                }) if **func == CExpr::Var("sym._unlock".to_string())
            ),
            "expected live unlock printf with prior atoi to keep helper result in final slot, got {printf_call_args:?}"
        );

        let stmts = ctx.fold_block(&block, block.addr);
        assert!(
            !stmts.iter().any(|stmt| matches!(
                stmt,
                CStmt::Expr(CExpr::Call { func, .. })
                    if **func == CExpr::Var("sym._unlock".to_string())
            )),
            "expected helper call to inline into printf, got {stmts:?}"
        );
        let Some(CStmt::Expr(CExpr::Call { args, .. })) = stmts.iter().find(|stmt| {
            matches!(
                stmt,
                CStmt::Expr(CExpr::Call { func, .. })
                    if **func == CExpr::Var("sym.imp.printf".to_string())
            )
        }) else {
            panic!("expected folded printf call, got {stmts:?}");
        };
        assert_eq!(
            args[0],
            CExpr::StringLit("unlock(%d, %d, %d) = %d\\n".to_string())
        );
        assert_eq!(args[1], CExpr::Var("local_2c".to_string()));
        assert_eq!(args[2], CExpr::Var("local_30".to_string()));
        let uncertified_third_arg = CExpr::call(
            CExpr::Var("sym.imp.atoi".to_string()),
            vec![CExpr::Subscript {
                base: Box::new(CExpr::Var("argv".to_string())),
                index: Box::new(CExpr::IntLit(4)),
            }],
        );
        assert_eq!(args[3], uncertified_third_arg);
        assert_eq!(
            args[4],
            CExpr::call(
                CExpr::Var("sym._unlock".to_string()),
                vec![
                    CExpr::IntLit(1),
                    CExpr::IntLit(2),
                    uncertified_third_arg,
                ],
            ),
            "uncertified printf sibling inputs must not be silently repaired, got {args:?}"
        );
    }

    #[test]
    fn folded_arm64_printf_live_unlock_shape_direct_result_store_preserves_uncertified_siblings() {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x1000005d4, "sym._unlock".to_string()),
            (0x10000259c, "sym.imp.printf".to_string()),
            (0x1000025d8, "sym.imp.atoi".to_string()),
        ])));
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x10000266f,
            "unlock(%d, %d, %d) = %d\\n".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym._unlock".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::Int(32), CType::Int(32), CType::Int(32)],
                    variadic: false,
                },
            ),
            (
                "sym.imp.printf".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: true,
                },
            ),
            (
                "sym.imp.atoi".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: false,
                },
            ),
        ]));
        ctx.set_external_stack_vars(HashMap::from([
            (
                -44,
                stack_var_spec("local_2c", Some(CType::Int(32)), Some("x29")),
            ),
            (
                -48,
                stack_var_spec("local_30", Some(CType::Int(32)), Some("x29")),
            ),
            (
                -52,
                stack_var_spec("local_34", Some(CType::Int(32)), Some("x29")),
            ),
        ]));
        ctx.inputs.visible_bindings = Box::leak(Box::new(vec![
            visible_stack_binding("local_2c", Some(CType::Int(32)), -44),
            visible_stack_binding("local_30", Some(CType::Int(32)), -48),
            visible_stack_binding("local_34", Some(CType::Int(32)), -52),
        ]));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([
            ("x0".to_string(), "argc".to_string()),
            ("x1".to_string(), "argv".to_string()),
            ("x2".to_string(), "envp".to_string()),
        ])));
        ctx.inputs.type_hints = Box::leak(Box::new(HashMap::from([
            ("argc".to_string(), CType::Int(32)),
            ("argv".to_string(), CType::ptr(CType::ptr(CType::Int(8)))),
            ("envp".to_string(), CType::ptr(CType::ptr(CType::Int(8)))),
        ])));

        let sp = make_var("SP", 2, 8);
        let fp = make_var("X29", 1, 8);
        let argv = make_var("X1", 0, 8);
        let local_a_slot = make_var("tmp:6980", 12, 8);
        let local_b_slot = make_var("tmp:6980", 13, 8);
        let local_c_slot = make_var("tmp:6980", 14, 8);
        let argv2_addr = make_var("tmp:6500", 20, 8);
        let argv3_addr = make_var("tmp:6500", 21, 8);
        let argv4_addr = make_var("tmp:6500", 22, 8);
        let helper_home_a = make_var("tmp:6500", 26, 8);
        let helper_home_b = make_var("tmp:6500", 27, 8);
        let helper_home_c = make_var("tmp:6500", 28, 8);
        let printf_home1 = make_var("tmp:6500", 32, 8);
        let printf_home2 = make_var("tmp:6500", 33, 8);
        let printf_home_ret = make_var("tmp:6500", 34, 8);

        let block = SSABlock {
            addr: 0x10000141c,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: argv2_addr.clone(),
                    a: argv.clone(),
                    b: make_var("const:10", 0, 8),
                },
                SSAOp::Load {
                    dst: make_var("X0", 8, 8),
                    space: "ram".to_string(),
                    addr: argv2_addr,
                },
                SSAOp::Call {
                    target: make_var("const:1000025d8", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("tmp:3a680", 5, 4),
                    src: make_var("W0", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: local_a_slot.clone(),
                    a: fp.clone(),
                    b: make_var("const:ffffffffffffffd4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: local_a_slot.clone(),
                    val: make_var("tmp:3a680", 5, 4),
                },
                SSAOp::IntAdd {
                    dst: argv3_addr.clone(),
                    a: argv.clone(),
                    b: make_var("const:18", 0, 8),
                },
                SSAOp::Load {
                    dst: make_var("X0", 9, 8),
                    space: "ram".to_string(),
                    addr: argv3_addr,
                },
                SSAOp::Call {
                    target: make_var("const:1000025d8", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("tmp:3a680", 6, 4),
                    src: make_var("W0", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: local_b_slot.clone(),
                    a: fp.clone(),
                    b: make_var("const:ffffffffffffffd0", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: local_b_slot.clone(),
                    val: make_var("tmp:3a680", 6, 4),
                },
                SSAOp::IntAdd {
                    dst: argv4_addr.clone(),
                    a: argv,
                    b: make_var("const:20", 0, 8),
                },
                SSAOp::Load {
                    dst: make_var("X0", 10, 8),
                    space: "ram".to_string(),
                    addr: argv4_addr,
                },
                SSAOp::Call {
                    target: make_var("const:1000025d8", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("tmp:3a680", 7, 4),
                    src: make_var("W0", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: local_c_slot.clone(),
                    a: fp.clone(),
                    b: make_var("const:ffffffffffffffcc", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: local_c_slot.clone(),
                    val: make_var("tmp:3a680", 7, 4),
                },
                SSAOp::Load {
                    dst: make_var("tmp:24d00", 8, 4),
                    space: "ram".to_string(),
                    addr: local_a_slot.clone(),
                },
                SSAOp::IntZExt {
                    dst: make_var("X8", 30, 8),
                    src: make_var("tmp:24d00", 8, 4),
                },
                SSAOp::IntAdd {
                    dst: helper_home_a.clone(),
                    a: sp.clone(),
                    b: make_var("const:150", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: helper_home_a.clone(),
                    val: make_var("X8", 30, 8),
                },
                SSAOp::Load {
                    dst: make_var("tmp:24d00", 9, 4),
                    space: "ram".to_string(),
                    addr: local_b_slot.clone(),
                },
                SSAOp::IntZExt {
                    dst: make_var("X8", 31, 8),
                    src: make_var("tmp:24d00", 9, 4),
                },
                SSAOp::IntAdd {
                    dst: helper_home_b.clone(),
                    a: sp.clone(),
                    b: make_var("const:158", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: helper_home_b.clone(),
                    val: make_var("X8", 31, 8),
                },
                SSAOp::Load {
                    dst: make_var("tmp:24d00", 10, 4),
                    space: "ram".to_string(),
                    addr: local_c_slot.clone(),
                },
                SSAOp::IntZExt {
                    dst: make_var("X8", 32, 8),
                    src: make_var("tmp:24d00", 10, 4),
                },
                SSAOp::IntAdd {
                    dst: helper_home_c.clone(),
                    a: sp.clone(),
                    b: make_var("const:160", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: helper_home_c.clone(),
                    val: make_var("X8", 32, 8),
                },
                SSAOp::Load {
                    dst: make_var("tmp:24d00", 11, 4),
                    space: "ram".to_string(),
                    addr: local_a_slot,
                },
                SSAOp::IntZExt {
                    dst: make_var("X0", 12, 8),
                    src: make_var("tmp:24d00", 11, 4),
                },
                SSAOp::Call {
                    target: make_var("const:1000005d4", 0, 8),
                },
                SSAOp::Load {
                    dst: make_var("X11", 2, 8),
                    space: "ram".to_string(),
                    addr: helper_home_a,
                },
                SSAOp::Load {
                    dst: make_var("X10", 3, 8),
                    space: "ram".to_string(),
                    addr: helper_home_b,
                },
                SSAOp::Load {
                    dst: make_var("X8", 33, 8),
                    space: "ram".to_string(),
                    addr: helper_home_c,
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: sp.clone(),
                    val: make_var("X11", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: printf_home1.clone(),
                    a: sp.clone(),
                    b: make_var("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: printf_home1,
                    val: make_var("X10", 3, 8),
                },
                SSAOp::IntAdd {
                    dst: printf_home2.clone(),
                    a: sp.clone(),
                    b: make_var("const:10", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: printf_home2,
                    val: make_var("X8", 33, 8),
                },
                SSAOp::IntAdd {
                    dst: printf_home_ret.clone(),
                    a: sp,
                    b: make_var("const:18", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: printf_home_ret,
                    val: make_var("X0", 12, 8),
                },
                SSAOp::Copy {
                    dst: make_var("X0", 14, 8),
                    src: make_var("const:10000266f", 0, 8),
                },
                SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
            ],
        };

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let printf_call_args = ctx
            .state
            .analysis_ctx
            .use_info
            .call_args
            .get(&(block.addr, block.ops.len() - 1))
            .expect("printf call args");
        let helper_call_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Call { target } if target.display_name() == "const:1000005d4_0"))
            .expect("helper call idx");
        assert!(
            matches!(
                printf_call_args.last(),
                Some(crate::analysis::CallArgBinding {
                    arg: crate::analysis::SemanticCallArg::FallbackExpr(CExpr::Call { func, .. }),
                    role: crate::analysis::CallArgRole::Result,
                    source_call: Some((source_block, source_idx)),
                    ..
                }) if **func == CExpr::Var("sym._unlock".to_string())
                    && *source_block == block.addr
                    && *source_idx == helper_call_idx
            ),
            "expected direct X0 result-store unlock printf to keep helper result in final slot, inlined={:?}, printf={printf_call_args:?}",
            ctx.state.analysis_ctx.use_info.inlined_call_results
        );
        let printf_stmt = ctx
            .op_to_stmt_with_args(
                block.ops.last().expect("printf call"),
                block.addr,
                block.ops.len() - 1,
            )
            .expect("printf stmt");
        let CStmt::Expr(CExpr::Call { args, .. }) = &printf_stmt else {
            panic!("expected lowered printf call, got {printf_stmt:?}");
        };
        assert_eq!(
            args[0],
            CExpr::StringLit("unlock(%d, %d, %d) = %d\\n".to_string())
        );
        assert_eq!(args[1], CExpr::Var("local_2c".to_string()));
        assert_eq!(args[2], CExpr::Var("local_30".to_string()));
        let atoi_arg = |index| {
            CExpr::call(
                CExpr::Var("sym.imp.atoi".to_string()),
                vec![CExpr::Subscript {
                    base: Box::new(CExpr::Var("argv".to_string())),
                    index: Box::new(CExpr::IntLit(index)),
                }],
            )
        };
        let uncertified_third_arg = atoi_arg(4);
        assert_eq!(args[3], uncertified_third_arg);
        assert_eq!(
            args[4],
            CExpr::call(
                CExpr::Var("sym._unlock".to_string()),
                vec![atoi_arg(2), atoi_arg(3), uncertified_third_arg],
            ),
            "uncertified printf sibling inputs must not be silently repaired, got {args:?}"
        );
    }

    #[test]
    fn decompile_x86_complex_check_keeps_named_local_carrier_and_concrete_returns() {
        use r2il::R2ILBlock;
        use r2ssa::SSAFunction;

        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1008, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut one = R2ILBlock::new(0x1004, 4);
        one.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });
        let mut zero = R2ILBlock::new(0x1008, 4);
        zero.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });
        let mut exit = R2ILBlock::new(0x100c, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        let blocks = vec![entry, one, zero, exit];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        func = func.with_name("sym._complex_check");

        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntSub {
                dst: make_var("tmp:diffcmp", 1, 4),
                a: make_var("EDI", 0, 4),
                b: make_var("const:0d100", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("ZF", 3, 1),
                a: make_var("tmp:diffcmp", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:cond", 1, 1),
                src: make_var("ZF", 3, 1),
            },
            SSAOp::CBranch {
                target: make_var("ram:1008", 0, 8),
                cond: make_var("tmp:cond", 1, 1),
            },
        ];
        func.get_block_mut(0x1004).expect("one").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:retaddr", 2, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:retaddr", 2, 8),
                val: make_var("const:1", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x1008).expect("zero").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:retaddr", 1, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:retaddr", 1, 8),
                val: make_var("const:0", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x100c).expect("exit").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("RSP", 2, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("RIP", 1, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 2, 8),
            },
            SSAOp::Return {
                target: make_var("RIP", 1, 8),
            },
        ];

        let mut decompiler = crate::Decompiler::new(crate::DecompilerConfig::x86_64());
        let signature = signature_spec(
            Some(crate::CType::Int(64)),
            vec![
                ("arg1", Some(crate::CType::Int(32))),
                ("arg2", Some(crate::CType::Int(32))),
            ],
        );
        decompiler.set_type_facts(FunctionTypeFacts {
            signature_certificate: external_signature_certificate(&signature),
            merged_signature: Some(signature),
            external_stack_vars: HashMap::from([(
                -4,
                stack_var_spec("var_4h", Some(crate::CType::Int(32)), Some("RBP")),
            )]),
            ..FunctionTypeFacts::default()
        });

        let mut ctx = make_x86_64_ctx();
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        ctx.analyze_blocks(&fold_blocks);
        ctx.analyze_function_structure(&func);

        let output = decompiler.decompile(&func);
        assert!(
            output.contains("int64_t sym._complex_check(int32_t arg1, int32_t arg2)"),
            "expected stable x86 header, got:\n{output}"
        );
        assert!(
            output.contains("if (arg1 != 100)")
                || output.contains("if (arg1 == 100)")
                || output.contains("if (arg1 != 0x64)")
                || output.contains("if (arg1 == 0x64)"),
            "expected recovered branch predicate, got:\n{output}"
        );
        assert!(
            output.contains("return 0;") && output.contains("return 1;"),
            "expected concrete branch returns, got:\n{output}"
        );
        assert!(
            !output.contains("tmp:") && !output.contains("saved_fp"),
            "complex_check should stay free of transient decompiler artifacts, got:\n{output}"
        );
        assert!(
            !output.contains("{\n    }\n"),
            "unexpected empty if body in:\n{output}"
        );
    }

    #[test]
    fn decompile_x86_solve_equation_fixture_shape_uses_arg_not_raw_stack_deref() {
        use r2il::R2ILBlock;
        use r2ssa::{PhiNode, SSAFunction};

        let mut entry = R2ILBlock::new(0x100000850, 0x18);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x100000871, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut then_block = R2ILBlock::new(0x100000868, 9);
        then_block.push(R2ILOp::Branch {
            target: Varnode::constant(0x100000878, 8),
        });
        let mut else_block = R2ILBlock::new(0x100000871, 7);
        else_block.push(R2ILOp::Branch {
            target: Varnode::constant(0x100000878, 8),
        });
        let mut exit = R2ILBlock::new(0x100000878, 5);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let blocks = vec![entry, then_block, else_block, exit];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        func = func.with_name("sym._solve_equation_fixture_shape");

        func.get_block_mut(0x100000850).expect("entry").ops = vec![
            SSAOp::Copy {
                dst: make_var("tmp:27d00", 1, 8),
                src: make_var("RBP", 0, 8),
            },
            SSAOp::IntSub {
                dst: make_var("RSP", 1, 8),
                a: make_var("RSP", 0, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("RSP", 1, 8),
                val: make_var("tmp:27d00", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("RBP", 1, 8),
                src: make_var("RSP", 1, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 1, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:6a80", 1, 4),
                src: make_var("EDI", 0, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 1, 8),
                val: make_var("tmp:6a80", 1, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 2, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 2, 8),
            },
            SSAOp::Copy {
                dst: make_var("EAX", 1, 4),
                src: make_var("tmp:11f00", 1, 4),
            },
            SSAOp::IntZExt {
                dst: make_var("RAX", 1, 8),
                src: make_var("EAX", 1, 4),
            },
            SSAOp::IntSLess {
                dst: make_var("CF", 1, 1),
                a: make_var("EAX", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntLeft {
                dst: make_var("EAX", 2, 4),
                a: make_var("EAX", 1, 4),
                b: make_var("const:1", 0, 4),
            },
            SSAOp::IntSLess {
                dst: make_var("tmp:69e80", 1, 1),
                a: make_var("EAX", 2, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntXor {
                dst: make_var("OF", 1, 1),
                a: make_var("CF", 1, 1),
                b: make_var("tmp:69e80", 1, 1),
            },
            SSAOp::IntZExt {
                dst: make_var("RAX", 2, 8),
                src: make_var("EAX", 2, 4),
            },
            SSAOp::IntSLess {
                dst: make_var("SF", 1, 1),
                a: make_var("EAX", 2, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("ZF", 1, 1),
                a: make_var("EAX", 2, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c200", 1, 4),
                a: make_var("EAX", 2, 4),
                b: make_var("const:ff", 0, 4),
            },
            SSAOp::PopCount {
                dst: make_var("tmp:2c280", 1, 4),
                src: make_var("tmp:2c200", 1, 4),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c300", 1, 4),
                a: make_var("tmp:2c280", 1, 4),
                b: make_var("const:1", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("PF", 1, 1),
                a: make_var("tmp:2c300", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntCarry {
                dst: make_var("CF", 2, 1),
                a: make_var("EAX", 2, 4),
                b: make_var("const:5", 0, 4),
            },
            SSAOp::IntSCarry {
                dst: make_var("OF", 2, 1),
                a: make_var("EAX", 2, 4),
                b: make_var("const:5", 0, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("EAX", 3, 4),
                a: make_var("EAX", 2, 4),
                b: make_var("const:5", 0, 4),
            },
            SSAOp::IntZExt {
                dst: make_var("RAX", 3, 8),
                src: make_var("EAX", 3, 4),
            },
            SSAOp::IntSLess {
                dst: make_var("SF", 2, 1),
                a: make_var("EAX", 3, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("ZF", 2, 1),
                a: make_var("EAX", 3, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c200", 2, 4),
                a: make_var("EAX", 3, 4),
                b: make_var("const:ff", 0, 4),
            },
            SSAOp::PopCount {
                dst: make_var("tmp:2c280", 2, 4),
                src: make_var("tmp:2c200", 2, 4),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c300", 2, 4),
                a: make_var("tmp:2c280", 2, 4),
                b: make_var("const:1", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("PF", 2, 1),
                a: make_var("tmp:2c300", 2, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 3, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:6a80", 2, 4),
                src: make_var("EAX", 3, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 3, 8),
                val: make_var("tmp:6a80", 2, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 4, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 2, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 4, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:3e900", 1, 4),
                src: make_var("tmp:11f00", 2, 4),
            },
            SSAOp::IntLess {
                dst: make_var("CF", 3, 1),
                a: make_var("tmp:3e900", 1, 4),
                b: make_var("const:19", 0, 4),
            },
            SSAOp::IntSBorrow {
                dst: make_var("OF", 3, 1),
                a: make_var("tmp:3e900", 1, 4),
                b: make_var("const:19", 0, 4),
            },
            SSAOp::IntSub {
                dst: make_var("tmp:3ea00", 1, 4),
                a: make_var("tmp:3e900", 1, 4),
                b: make_var("const:19", 0, 4),
            },
            SSAOp::IntSLess {
                dst: make_var("SF", 3, 1),
                a: make_var("tmp:3ea00", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("ZF", 3, 1),
                a: make_var("tmp:3ea00", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c200", 3, 4),
                a: make_var("tmp:3ea00", 1, 4),
                b: make_var("const:ff", 0, 4),
            },
            SSAOp::PopCount {
                dst: make_var("tmp:2c280", 3, 4),
                src: make_var("tmp:2c200", 3, 4),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c300", 3, 4),
                a: make_var("tmp:2c280", 3, 4),
                b: make_var("const:1", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("PF", 3, 1),
                a: make_var("tmp:2c300", 3, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:12800", 1, 1),
                src: make_var("ZF", 3, 1),
            },
            SSAOp::CBranch {
                target: make_var("ram:100000871", 0, 8),
                cond: make_var("tmp:12800", 1, 1),
            },
        ];
        func.get_block_mut(0x100000868).expect("then").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 5, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 5, 8),
                val: make_var("const:1", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:100000878", 0, 8),
            },
        ];
        func.get_block_mut(0x100000871).expect("else").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 6, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 6, 8),
                val: make_var("const:0", 0, 4),
            },
        ];
        func.get_block_mut(0x100000878).expect("exit").phis = vec![
            PhiNode {
                dst: make_var("tmp:4700", 7, 8),
                sources: vec![
                    (0x100000868, make_var("tmp:4700", 0, 8)),
                    (0x100000871, make_var("tmp:4700", 0, 8)),
                ],
            },
            PhiNode {
                dst: make_var("tmp:6a80", 5, 4),
                sources: vec![
                    (0x100000868, make_var("tmp:6a80", 0, 4)),
                    (0x100000871, make_var("tmp:6a80", 0, 4)),
                ],
            },
        ];
        func.get_block_mut(0x100000878).expect("exit").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 8, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 3, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 8, 8),
            },
            SSAOp::Copy {
                dst: make_var("EAX", 4, 4),
                src: make_var("tmp:11f00", 3, 4),
            },
            SSAOp::IntZExt {
                dst: make_var("RAX", 4, 8),
                src: make_var("EAX", 4, 4),
            },
            SSAOp::Copy {
                dst: make_var("tmp:55400", 1, 8),
                src: make_var("const:0", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:55400", 2, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 1, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("RSP", 2, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("RBP", 2, 8),
                src: make_var("tmp:55400", 2, 8),
            },
            SSAOp::Load {
                dst: make_var("RIP", 1, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 2, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("RSP", 3, 8),
                a: make_var("RSP", 2, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Return {
                target: make_var("RIP", 1, 8),
            },
        ];

        let mut ctx = make_x86_64_ctx();
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        ctx.analyze_blocks(&fold_blocks);
        ctx.analyze_function_structure(&func);

        let cond = ctx
            .extract_condition_from_block(func.get_block(0x100000850).expect("entry"))
            .expect("solve_equation condition");
        let expected_arithmetic = CExpr::binary(
            BinaryOp::Ne,
            CExpr::binary(
                BinaryOp::Add,
                CExpr::binary(
                    BinaryOp::Shl,
                    CExpr::Var("arg1".to_string()),
                    CExpr::IntLit(1),
                ),
                CExpr::IntLit(5),
            ),
            CExpr::IntLit(25),
        );
        let expected_named_local = CExpr::binary(
            BinaryOp::Ne,
            CExpr::Var("local_c".to_string()),
            CExpr::IntLit(25),
        );
        assert!(
            cond == expected_arithmetic || cond == expected_named_local,
            "expected solve_equation to stay source-like or at least collapse to a named local, got {cond:?}"
        );

        let mut decompiler = crate::Decompiler::new(crate::DecompilerConfig::x86_64());
        let signature = signature_spec(
            Some(crate::CType::Int(64)),
            vec![("arg1", Some(crate::CType::Int(32)))],
        );
        decompiler.set_type_facts(FunctionTypeFacts {
            signature_certificate: external_signature_certificate(&signature),
            merged_signature: Some(signature),
            external_stack_vars: HashMap::from([
                (
                    -12,
                    stack_var_spec("var_ch", Some(crate::CType::Int(32)), Some("RBP")),
                ),
                (
                    -8,
                    stack_var_spec(
                        "var_8h",
                        Some(crate::CType::Pointer(Box::new(crate::CType::Void))),
                        Some("RBP"),
                    ),
                ),
                (
                    -4,
                    stack_var_spec("var_4h", Some(crate::CType::Int(32)), Some("RBP")),
                ),
                (
                    8,
                    stack_var_spec("var_8h", Some(crate::CType::Int(64)), Some("RBP")),
                ),
            ]),
            ..FunctionTypeFacts::default()
        });

        let output = decompiler.decompile(&func);
        assert!(
            output.contains("int64_t sym._solve_equation_fixture_shape(int32_t arg1)"),
            "unexpected function signature:\n{output}"
        );
        assert!(
            output.contains("if ((arg1 << 1) + 5 != 25)")
                || output.contains("if (var_ch != 25)"),
            "expected arg-backed or at least named-local scalar condition, got:\n{output}"
        );
        assert!(
            !output.contains("*(rbp"),
            "unexpected raw frame deref in:\n{output}"
        );
    }

    #[test]
    fn decompile_x86_no_calldefine_strcmp_condition_does_not_collapse() {
        use r2il::R2ILBlock;
        use r2ssa::SSAFunction;

        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1008, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut fail = R2ILBlock::new(0x1004, 4);
        fail.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut pass = R2ILBlock::new(0x1008, 4);
        pass.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let blocks = vec![entry, fail, pass];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        func = func.with_name("sym._authenticate_fixture_shape");

        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::Copy {
                dst: make_var("RSI", 1, 8),
                src: make_var("const:403014", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("RDI", 1, 8),
                src: make_var("RDI", 0, 8),
            },
            SSAOp::Call {
                target: make_var("ram:401130", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("CF", 2, 1),
                src: make_var("const:0", 0, 1),
            },
            SSAOp::Copy {
                dst: make_var("OF", 2, 1),
                src: make_var("const:0", 0, 1),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:70400", 1, 4),
                a: make_var("EAX", 0, 4),
                b: make_var("EAX", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("ZF", 2, 1),
                a: make_var("tmp:70400", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:12800", 1, 1),
                src: make_var("ZF", 2, 1),
            },
            SSAOp::CBranch {
                cond: make_var("tmp:12800", 1, 1),
                target: make_var("ram:1008", 0, 8),
            },
        ];
        func.get_block_mut(0x1004).expect("fail").ops = vec![
            SSAOp::Copy {
                dst: make_var("RAX", 1, 8),
                src: make_var("const:1", 0, 8),
            },
            SSAOp::Return {
                target: make_var("RAX", 1, 8),
            },
        ];
        func.get_block_mut(0x1008).expect("pass").ops = vec![
            SSAOp::Copy {
                dst: make_var("RAX", 2, 8),
                src: make_var("const:0", 0, 8),
            },
            SSAOp::Return {
                target: make_var("RAX", 2, 8),
            },
        ];

        let mut decompiler = crate::Decompiler::new(crate::DecompilerConfig::x86_64());
        decompiler.set_function_names(HashMap::from([(0x401130, "sym.imp.strcmp".to_string())]));
        decompiler.set_strings(HashMap::from([(0x403014, "secret123".to_string())]));
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(crate::CType::Int(32)),
                vec![("password", Some(crate::CType::ptr(crate::CType::Int(8))))],
            )),
            known_function_signatures: HashMap::from([(
                "sym.imp.strcmp".to_string(),
                r2types::FunctionType {
                    return_type: r2types::CTypeLike::Int {
                        bits: 32,
                        signedness: r2types::Signedness::Signed,
                    },
                    params: vec![
                        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Int {
                            bits: 8,
                            signedness: r2types::Signedness::Signed,
                        })),
                        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Int {
                            bits: 8,
                            signedness: r2types::Signedness::Signed,
                        })),
                    ],
                    variadic: false,
                },
            )]),
            ..FunctionTypeFacts::default()
        });

        let output = decompiler.decompile(&func);
        assert!(
            !output.contains("0 != 0"),
            "no-calldefine strcmp condition should not collapse to a constant, got:\n{output}"
        );
        assert!(
            output.contains("sym.imp.strcmp"),
            "expected strcmp call to survive in the decompiled output, got:\n{output}"
        );
    }

    #[test]
    fn decompile_x86_bool_carrier_chain_reconstructs_scalar_condition_and_returns() {
        use r2il::R2ILBlock;
        use r2ssa::SSAFunction;

        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1008, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut fallthrough = R2ILBlock::new(0x1004, 4);
        fallthrough.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });
        let mut taken = R2ILBlock::new(0x1008, 4);
        taken.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });
        let mut exit = R2ILBlock::new(0x100c, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let blocks = vec![entry, fallthrough, taken, exit];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        func = func.with_name("sym._test_bool_carrier_chain");

        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntSub {
                dst: make_var("RSP", 1, 8),
                a: make_var("RSP", 0, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::IntNotEqual {
                dst: make_var("tmp:neq", 1, 1),
                a: make_var("EDI", 0, 4),
                b: make_var("ESI", 0, 4),
            },
            SSAOp::IntZExt {
                dst: make_var("tmp:widen", 1, 4),
                src: make_var("tmp:neq", 1, 1),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:condaddr", 1, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:condaddr", 1, 8),
                val: make_var("tmp:widen", 1, 4),
            },
            SSAOp::Load {
                dst: make_var("tmp:condreload", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:condaddr", 1, 8),
            },
            SSAOp::IntNotEqual {
                dst: make_var("tmp:branch", 1, 1),
                a: make_var("tmp:condreload", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::CBranch {
                target: make_var("ram:1008", 0, 8),
                cond: make_var("tmp:branch", 1, 1),
            },
        ];
        func.get_block_mut(0x1004).expect("else").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:retaddr", 1, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:retaddr", 1, 8),
                val: make_var("ESI", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x1008).expect("then").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:retaddr", 2, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:retaddr", 2, 8),
                val: make_var("EDI", 0, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x100c).expect("exit").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("RSP", 2, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("RIP", 1, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 2, 8),
            },
            SSAOp::Return {
                target: make_var("RIP", 1, 8),
            },
        ];

        let mut ctx = make_x86_64_ctx();
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        ctx.analyze_blocks(&fold_blocks);
        ctx.analyze_function_structure(&func);

        let cond_slot = ctx
            .debug_stack_slot_provenance("tmp:condreload_1")
            .expect("predicate carrier slot");
        assert!(cond_slot.is_scalar_predicate_carrier(), "{cond_slot:?}");
        let ret_slot = ctx
            .debug_stack_slot_provenance("tmp:retaddr_1")
            .expect("return carrier slot");
        assert!(ret_slot.is_scalar_return_carrier(), "{ret_slot:?}");

        let entry = func.get_block(0x1000).expect("entry");
        let cond = ctx
            .extract_condition_from_block(entry)
            .expect("scalarized condition");
        assert_eq!(
            cond,
            CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("arg1".to_string()),
                CExpr::Var("arg2".to_string()),
            )
        );

        let then_stmts = ctx.fold_block(func.get_block(0x1008).expect("then"), 0x1008);
        let else_stmts = ctx.fold_block(func.get_block(0x1004).expect("else"), 0x1004);
        let Some(CStmt::Return(Some(then_expr))) = then_stmts.last() else {
            panic!("then block should fold to a scalar return, got {then_stmts:?}");
        };
        let Some(CStmt::Return(Some(else_expr))) = else_stmts.last() else {
            panic!("else block should fold to a scalar return, got {else_stmts:?}");
        };
        assert_eq!(then_expr, &CExpr::Var("arg1".to_string()));
        assert_eq!(else_expr, &CExpr::Var("arg2".to_string()));

        let mut decompiler = crate::Decompiler::new(crate::DecompilerConfig::x86_64());
        let signature = signature_spec(
            Some(crate::CType::Int(64)),
            vec![
                ("arg1", Some(crate::CType::Int(32))),
                ("arg2", Some(crate::CType::Int(32))),
            ],
        );
        decompiler.set_type_facts(FunctionTypeFacts {
            signature_certificate: external_signature_certificate(&signature),
            merged_signature: Some(signature),
            external_stack_vars: HashMap::from([
                (
                    -4,
                    stack_var_spec("var_4h", Some(crate::CType::Int(32)), Some("RBP")),
                ),
                (
                    -8,
                    stack_var_spec("var_8h", Some(crate::CType::UInt(32)), Some("RBP")),
                ),
            ]),
            ..FunctionTypeFacts::default()
        });

        let output = decompiler.decompile(&func);
        assert!(
            output.contains("int64_t sym._test_bool_carrier_chain(int32_t arg1, int32_t arg2)"),
            "unexpected function signature:\n{output}"
        );
        assert!(
            output.contains("if (arg1 != arg2)"),
            "expected source-like scalar branch condition, got:\n{output}"
        );
        assert!(
            output.contains("return arg1;") && output.contains("return arg2;"),
            "expected scalar branch-selected returns, got:\n{output}"
        );
        for bad in ["rbp", "rsp", "&var_", "*(", "var_4h =", "var_8h"] {
            assert!(
                !output.contains(bad),
                "unexpected stack/address artifact {bad:?} in:\n{output}"
            );
        }
    }

    #[test]
    fn decompile_x86_bool_carrier_chain_fixture_shape_reconstructs_source_like_output() {
        use r2il::R2ILBlock;
        use r2ssa::{PhiNode, SSAFunction};

        let mut entry = R2ILBlock::new(0x100001050, 0x2a);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x100001082, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut fallthrough = R2ILBlock::new(0x10000107a, 8);
        fallthrough.push(R2ILOp::Branch {
            target: Varnode::constant(0x100001088, 8),
        });
        let mut taken = R2ILBlock::new(0x100001082, 6);
        taken.push(R2ILOp::Branch {
            target: Varnode::constant(0x100001088, 8),
        });
        let mut exit = R2ILBlock::new(0x100001088, 5);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let blocks = vec![entry, fallthrough, taken, exit];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        func = func.with_name("sym._test_bool_carrier_chain_fixture_shape");

        func.get_block_mut(0x100001050).expect("entry").ops = vec![
            SSAOp::Copy {
                dst: make_var("tmp:27d00", 1, 8),
                src: make_var("RBP", 0, 8),
            },
            SSAOp::IntSub {
                dst: make_var("RSP", 1, 8),
                a: make_var("RSP", 0, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("RSP", 1, 8),
                val: make_var("tmp:27d00", 1, 8),
            },
            SSAOp::Copy {
                dst: make_var("RBP", 1, 8),
                src: make_var("RSP", 1, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 1, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:6a80", 1, 4),
                src: make_var("EDI", 0, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 1, 8),
                val: make_var("tmp:6a80", 1, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 2, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:6a80", 2, 4),
                src: make_var("ESI", 0, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 2, 8),
                val: make_var("tmp:6a80", 2, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 3, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 1, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 3, 8),
            },
            SSAOp::Copy {
                dst: make_var("EAX", 1, 4),
                src: make_var("tmp:11f00", 1, 4),
            },
            SSAOp::IntZExt {
                dst: make_var("RAX", 1, 8),
                src: make_var("EAX", 1, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 4, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:6a80", 3, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 4, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:3f680", 1, 4),
                src: make_var("tmp:6a80", 3, 4),
            },
            SSAOp::IntLess {
                dst: make_var("CF", 1, 1),
                a: make_var("EAX", 1, 4),
                b: make_var("tmp:3f680", 1, 4),
            },
            SSAOp::IntSBorrow {
                dst: make_var("OF", 1, 1),
                a: make_var("EAX", 1, 4),
                b: make_var("tmp:3f680", 1, 4),
            },
            SSAOp::IntSub {
                dst: make_var("tmp:3f780", 1, 4),
                a: make_var("EAX", 1, 4),
                b: make_var("tmp:3f680", 1, 4),
            },
            SSAOp::IntSLess {
                dst: make_var("SF", 1, 1),
                a: make_var("tmp:3f780", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("ZF", 1, 1),
                a: make_var("tmp:3f780", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c200", 1, 4),
                a: make_var("tmp:3f780", 1, 4),
                b: make_var("const:ff", 0, 4),
            },
            SSAOp::PopCount {
                dst: make_var("tmp:2c280", 1, 4),
                src: make_var("tmp:2c200", 1, 4),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c300", 1, 4),
                a: make_var("tmp:2c280", 1, 4),
                b: make_var("const:1", 0, 4),
            },
            SSAOp::IntEqual {
                dst: make_var("PF", 1, 1),
                a: make_var("tmp:2c300", 1, 4),
                b: make_var("const:0", 0, 4),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:12800", 1, 1),
                src: make_var("ZF", 1, 1),
            },
            SSAOp::Copy {
                dst: make_var("AL", 1, 1),
                src: make_var("tmp:12800", 1, 1),
            },
            SSAOp::Copy {
                dst: make_var("CF", 2, 1),
                src: make_var("const:0", 0, 1),
            },
            SSAOp::Copy {
                dst: make_var("OF", 2, 1),
                src: make_var("const:0", 0, 1),
            },
            SSAOp::IntAnd {
                dst: make_var("AL", 2, 1),
                a: make_var("AL", 1, 1),
                b: make_var("const:1", 0, 1),
            },
            SSAOp::IntSLess {
                dst: make_var("SF", 2, 1),
                a: make_var("AL", 2, 1),
                b: make_var("const:0", 0, 1),
            },
            SSAOp::IntEqual {
                dst: make_var("ZF", 2, 1),
                a: make_var("AL", 2, 1),
                b: make_var("const:0", 0, 1),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c200", 2, 1),
                a: make_var("AL", 2, 1),
                b: make_var("const:ff", 0, 1),
            },
            SSAOp::PopCount {
                dst: make_var("tmp:2c280", 2, 1),
                src: make_var("tmp:2c200", 2, 1),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c300", 2, 1),
                a: make_var("tmp:2c280", 2, 1),
                b: make_var("const:1", 0, 1),
            },
            SSAOp::IntEqual {
                dst: make_var("PF", 2, 1),
                a: make_var("tmp:2c300", 2, 1),
                b: make_var("const:0", 0, 1),
            },
            SSAOp::IntZExt {
                dst: make_var("EAX", 2, 4),
                src: make_var("AL", 2, 1),
            },
            SSAOp::IntZExt {
                dst: make_var("RAX", 2, 8),
                src: make_var("EAX", 2, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 5, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff0", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:6a80", 4, 4),
                src: make_var("EAX", 2, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 5, 8),
                val: make_var("tmp:6a80", 4, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 6, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff0", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 2, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 6, 8),
            },
            SSAOp::IntSExt {
                dst: make_var("RAX", 3, 8),
                src: make_var("tmp:11f00", 2, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 7, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:ffffffffffffffe8", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:6b00", 1, 8),
                src: make_var("RAX", 3, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 7, 8),
                val: make_var("tmp:6b00", 1, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 8, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:ffffffffffffffe8", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 1, 8),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 8, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:3ea80", 1, 8),
                src: make_var("tmp:11f80", 1, 8),
            },
            SSAOp::IntLess {
                dst: make_var("CF", 3, 1),
                a: make_var("tmp:3ea80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntSBorrow {
                dst: make_var("OF", 3, 1),
                a: make_var("tmp:3ea80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntSub {
                dst: make_var("tmp:3eb80", 1, 8),
                a: make_var("tmp:3ea80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntSLess {
                dst: make_var("SF", 3, 1),
                a: make_var("tmp:3eb80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntEqual {
                dst: make_var("ZF", 3, 1),
                a: make_var("tmp:3eb80", 1, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c200", 3, 8),
                a: make_var("tmp:3eb80", 1, 8),
                b: make_var("const:ff", 0, 8),
            },
            SSAOp::PopCount {
                dst: make_var("tmp:2c280", 3, 8),
                src: make_var("tmp:2c200", 3, 8),
            },
            SSAOp::IntAnd {
                dst: make_var("tmp:2c300", 3, 8),
                a: make_var("tmp:2c280", 3, 8),
                b: make_var("const:1", 0, 8),
            },
            SSAOp::IntEqual {
                dst: make_var("PF", 3, 1),
                a: make_var("tmp:2c300", 3, 8),
                b: make_var("const:0", 0, 8),
            },
            SSAOp::BoolNot {
                dst: make_var("tmp:12800", 2, 1),
                src: make_var("ZF", 3, 1),
            },
            SSAOp::CBranch {
                target: make_var("ram:100001082", 0, 8),
                cond: make_var("tmp:12800", 2, 1),
            },
        ];
        func.get_block_mut(0x10000107a).expect("else").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 9, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 3, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 9, 8),
            },
            SSAOp::Copy {
                dst: make_var("EAX", 3, 4),
                src: make_var("tmp:11f00", 3, 4),
            },
            SSAOp::IntZExt {
                dst: make_var("RAX", 4, 8),
                src: make_var("EAX", 3, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 10, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:6a80", 5, 4),
                src: make_var("EAX", 3, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 10, 8),
                val: make_var("tmp:6a80", 5, 4),
            },
            SSAOp::Branch {
                target: make_var("ram:100001088", 0, 8),
            },
        ];
        func.get_block_mut(0x100001082).expect("then").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 11, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 4, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 11, 8),
            },
            SSAOp::Copy {
                dst: make_var("EAX", 4, 4),
                src: make_var("tmp:11f00", 4, 4),
            },
            SSAOp::IntZExt {
                dst: make_var("RAX", 5, 8),
                src: make_var("EAX", 4, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 12, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("tmp:6a80", 6, 4),
                src: make_var("EAX", 4, 4),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 12, 8),
                val: make_var("tmp:6a80", 6, 4),
            },
        ];
        func.get_block_mut(0x100001088).expect("exit").phis = vec![
            PhiNode {
                dst: make_var("EAX", 5, 4),
                sources: vec![
                    (0x10000107a, make_var("EAX", 0, 4)),
                    (0x100001082, make_var("EAX", 0, 4)),
                ],
            },
            PhiNode {
                dst: make_var("RAX", 6, 8),
                sources: vec![
                    (0x10000107a, make_var("RAX", 0, 8)),
                    (0x100001082, make_var("RAX", 0, 8)),
                ],
            },
            PhiNode {
                dst: make_var("tmp:11f00", 5, 4),
                sources: vec![
                    (0x10000107a, make_var("tmp:11f00", 0, 4)),
                    (0x100001082, make_var("tmp:11f00", 0, 4)),
                ],
            },
            PhiNode {
                dst: make_var("tmp:4700", 13, 8),
                sources: vec![
                    (0x10000107a, make_var("tmp:4700", 0, 8)),
                    (0x100001082, make_var("tmp:4700", 0, 8)),
                ],
            },
            PhiNode {
                dst: make_var("tmp:6a80", 7, 4),
                sources: vec![
                    (0x10000107a, make_var("tmp:6a80", 0, 4)),
                    (0x100001082, make_var("tmp:6a80", 0, 4)),
                ],
            },
        ];
        func.get_block_mut(0x100001088).expect("exit").ops = vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 14, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 6, 4),
                space: "ram".to_string(),
                addr: make_var("tmp:4700", 14, 8),
            },
            SSAOp::Copy {
                dst: make_var("EAX", 6, 4),
                src: make_var("tmp:11f00", 6, 4),
            },
            SSAOp::IntZExt {
                dst: make_var("RAX", 7, 8),
                src: make_var("EAX", 6, 4),
            },
            SSAOp::Copy {
                dst: make_var("tmp:55400", 1, 8),
                src: make_var("const:0", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:55400", 2, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 1, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("RSP", 2, 8),
                a: make_var("RSP", 1, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Copy {
                dst: make_var("RBP", 2, 8),
                src: make_var("tmp:55400", 2, 8),
            },
            SSAOp::Load {
                dst: make_var("RIP", 1, 8),
                space: "ram".to_string(),
                addr: make_var("RSP", 2, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("RSP", 3, 8),
                a: make_var("RSP", 2, 8),
                b: make_var("const:8", 0, 8),
            },
            SSAOp::Return {
                target: make_var("RIP", 1, 8),
            },
        ];

        let mut ctx = make_x86_64_ctx();
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        ctx.analyze_blocks(&fold_blocks);
        ctx.analyze_function_structure(&func);

        let cond_slot = ctx
            .debug_stack_slot_provenance("tmp:11f80_1")
            .expect("predicate carrier slot");
        assert!(cond_slot.is_scalar_predicate_carrier(), "{cond_slot:?}");
        let ret_slot = ctx
            .debug_stack_slot_provenance("tmp:4700_10")
            .expect("return carrier slot");
        assert!(ret_slot.is_scalar_return_carrier(), "{ret_slot:?}");

        let entry = func.get_block(0x100001050).expect("entry");
        let cond = ctx
            .extract_condition_from_block(entry)
            .expect("scalarized condition");
        assert_eq!(
            cond,
            CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("arg1".to_string()),
                CExpr::Var("arg2".to_string()),
            )
        );
        let then_stmts = ctx.fold_block(func.get_block(0x100001082).expect("then"), 0x100001082);
        let else_stmts = ctx.fold_block(func.get_block(0x10000107a).expect("else"), 0x10000107a);
        assert_eq!(
            then_stmts,
            vec![CStmt::Return(Some(CExpr::Var("arg1".to_string())))]
        );
        assert_eq!(
            else_stmts,
            vec![CStmt::Return(Some(CExpr::Var("arg2".to_string())))]
        );

        let mut decompiler = crate::Decompiler::new(crate::DecompilerConfig::x86_64());
        let signature = signature_spec(
            Some(crate::CType::Int(64)),
            vec![
                ("arg1", Some(crate::CType::Int(32))),
                ("arg2", Some(crate::CType::Int(32))),
            ],
        );
        decompiler.set_type_facts(FunctionTypeFacts {
            signature_certificate: external_signature_certificate(&signature),
            merged_signature: Some(signature),
            external_stack_vars: HashMap::from([
                (
                    -4,
                    stack_var_spec("var_4h", Some(crate::CType::Int(32)), Some("RBP")),
                ),
                (
                    -8,
                    stack_var_spec("var_8h", Some(crate::CType::Int(32)), Some("RBP")),
                ),
                (
                    -12,
                    stack_var_spec("var_ch", Some(crate::CType::Int(32)), Some("RBP")),
                ),
                (
                    -16,
                    stack_var_spec("var_10h", Some(crate::CType::UInt(32)), Some("RBP")),
                ),
                (
                    -24,
                    stack_var_spec("var_18h", Some(crate::CType::Int(64)), Some("RBP")),
                ),
            ]),
            ..FunctionTypeFacts::default()
        });

        let output = decompiler.decompile(&func);
        assert!(
            output.contains(
                "int64_t sym._test_bool_carrier_chain_fixture_shape(int32_t arg1, int32_t arg2)"
            ),
            "unexpected function signature:\n{output}"
        );
        assert!(
            output.contains("if (arg1 != arg2)"),
            "expected source-like scalar branch condition, got:\n{output}"
        );
        assert!(
            output.contains("return arg1;") && output.contains("return arg2;"),
            "expected scalar branch-selected returns, got:\n{output}"
        );
        for bad in ["rbp", "rsp", "&var_", "*(", "var_4h =", "var_8h", "var_ch"] {
            assert!(
                !output.contains(bad),
                "unexpected stack/address artifact {bad:?} in:\n{output}"
            );
        }
    }

    #[test]
    fn scalar_context_visible_expr_ranking_prefers_scalar_candidates_over_stack_artifacts() {
        let mut ctx = make_x86_64_ctx();
        ctx.state.analysis_ctx.use_info.stack_slots.insert(
            "var_8h".to_string(),
            crate::analysis::StackSlotProvenance {
                offset: -8,
                predicate_carrier: true,
                return_carrier: false,
                value_kind: crate::analysis::StackSlotValueKind::Scalar,
            },
        );
        ctx.state.analysis_ctx.use_info.stack_slots.insert(
            "var_ch".to_string(),
            crate::analysis::StackSlotProvenance {
                offset: -12,
                predicate_carrier: false,
                return_carrier: true,
                value_kind: crate::analysis::StackSlotValueKind::Scalar,
            },
        );

        let raw_stack_load = CExpr::Deref(Box::new(CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("rbp".to_string()),
            CExpr::IntLit(-8),
        )));
        let raw_return_stack_load = CExpr::Deref(Box::new(CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("rbp".to_string()),
            CExpr::IntLit(-12),
        )));
        let scalar_arg1 = CExpr::Var("arg1".to_string());
        assert_eq!(
            ctx.debug_choose_scalar_predicate_expr(
                Some(raw_stack_load.clone()),
                Some(scalar_arg1.clone()),
            ),
            Some(scalar_arg1.clone())
        );
        assert_eq!(
            ctx.debug_choose_scalar_predicate_expr(
                Some(CExpr::AddrOf(Box::new(CExpr::Var("var_8h".to_string())))),
                Some(scalar_arg1.clone()),
            ),
            Some(scalar_arg1.clone())
        );

        let scalar_arg2 = CExpr::Var("arg2".to_string());
        assert_eq!(
            ctx.debug_choose_scalar_return_expr(
                Some(CExpr::AddrOf(Box::new(CExpr::Var("var_ch".to_string())))),
                Some(scalar_arg2.clone()),
            ),
            Some(scalar_arg2.clone())
        );
        assert_eq!(
            ctx.debug_choose_scalar_return_expr(
                Some(raw_return_stack_load),
                Some(scalar_arg2.clone()),
            ),
            Some(scalar_arg2.clone())
        );

        assert_eq!(
            ctx.debug_choose_generic_visible_expr(
                Some(CExpr::Var("arg1".to_string())),
                Some(CExpr::AddrOf(Box::new(CExpr::Var("var_8h".to_string())))),
            ),
            Some(CExpr::AddrOf(Box::new(CExpr::Var("var_8h".to_string()))))
        );
    }

    #[test]
    fn prepared_predicate_operand_prefers_visible_stack_owner_over_tmp_load() {
        let mut ctx = make_x86_64_ctx();
        ctx.set_external_stack_vars(HashMap::from([(
            -4,
            stack_var_spec("var_4h", Some(crate::CType::Int(32)), Some("RBP")),
        )]));
        ctx.state.analysis_ctx.use_info.stack_slots.insert(
            "tmp:11f00_1".to_string(),
            crate::analysis::StackSlotProvenance {
                offset: -4,
                predicate_carrier: true,
                return_carrier: false,
                value_kind: crate::analysis::StackSlotValueKind::Scalar,
            },
        );

        assert_eq!(
            ctx.debug_resolve_prepared_predicate_operand(&make_var("tmp:11f00", 1, 4)),
            CExpr::Var("var_4h".to_string())
        );
    }

    #[test]
    fn folded_x86_printf_result_slot_preserves_uncertified_sibling_args() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x1000005d4, "sym._unlock".to_string()),
            (0x10000259c, "sym.imp.printf".to_string()),
        ])));
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x1000027a0,
            "unlock(%d, %d, %d) = %d\\n".to_string(),
        )])));
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym._unlock".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::Int(32), CType::Int(32), CType::Int(32)],
                    variadic: false,
                },
            ),
            (
                "sym.imp.printf".to_string(),
                FunctionType {
                    return_type: CType::Int(32),
                    params: vec![CType::ptr(CType::Int(8))],
                    variadic: true,
                },
            ),
        ]));

        let helper_call_idx = 3usize;
        let block = SSABlock {
            addr: 0x2000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Copy {
                    dst: make_var("RDI", 1, 8),
                    src: make_var("const:1", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("RSI", 1, 8),
                    src: make_var("const:2", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("RDX", 1, 8),
                    src: make_var("const:3", 0, 8),
                },
                SSAOp::Call {
                    target: make_var("const:1000005d4", 0, 8),
                },
                SSAOp::CallDefine {
                    dst: make_var("EAX", 1, 4),
                },
                SSAOp::Copy {
                    dst: make_var("RDI", 2, 8),
                    src: make_var("const:1000027a0", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("RSI", 2, 8),
                    src: make_var("const:1", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("RDX", 2, 8),
                    src: make_var("const:2", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("RCX", 1, 8),
                    src: make_var("const:3", 0, 8),
                },
                SSAOp::Copy {
                    dst: make_var("R8", 1, 8),
                    src: make_var("EAX", 1, 4),
                },
                SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
            ],
        };

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let printf_call_args = ctx
            .state
            .analysis_ctx
            .use_info
            .call_args
            .get(&(block.addr, block.ops.len() - 1))
            .expect("printf call args");
        assert!(
            matches!(
                printf_call_args.last(),
                Some(crate::analysis::CallArgBinding {
                    arg: crate::analysis::SemanticCallArg::FallbackExpr(CExpr::Call { func, args }),
                    role: crate::analysis::CallArgRole::Result,
                    source_call: Some((source_block, source_idx)),
                    ..
                }) if **func == CExpr::Var("sym._unlock".to_string())
                    && args == &vec![CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]
                    && *source_block == block.addr
                    && *source_idx == helper_call_idx
            ),
            "expected x86 printf result slot to recover helper call from EAX alias, got {printf_call_args:?}"
        );

        let stmts = ctx.fold_block(&block, block.addr);
        assert_eq!(
            stmts.len(),
            1,
            "expected helper call to inline into printf, got {stmts:?}"
        );
        let CStmt::Expr(CExpr::Call { func, args }) = &stmts[0] else {
            panic!("expected folded printf call, got {stmts:?}");
        };
        assert_eq!(**func, CExpr::Var("sym.imp.printf".to_string()));
        assert_eq!(
            args,
            &vec![
                CExpr::StringLit("unlock(%d, %d, %d) = %d\\n".to_string()),
                CExpr::IntLit(1),
                CExpr::IntLit(2),
                CExpr::IntLit(3),
                CExpr::call(
                    CExpr::Var("sym._unlock".to_string()),
                    vec![CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)],
                ),
            ]
        );
    }

    #[test]
    fn imported_printf_stack_backed_pointer_arg_without_named_positive_base_renders_visible_storage()
     {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x1000_1000,
            "Copied: %s\\n".to_string(),
        )])));

        let rendered = ctx.render_call_args_for_callee(
            &CExpr::Var("sym.imp.printf".to_string()),
            vec![
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::StringAddr(0x1000_1000),
                ),
                crate::analysis::CallArgBinding::input(crate::analysis::SemanticCallArg::semantic(
                    crate::analysis::SemanticValue::Load {
                        addr: crate::analysis::NormalizedAddr {
                            base: crate::analysis::BaseRef::StackSlot(0x3e0),
                            index: None,
                            scale_bytes: 0,
                            offset_bytes: 312,
                        },
                        size: 8,
                    },
                )),
            ],
        );

        assert_eq!(
            rendered,
            if rendered[1] == CExpr::UIntLit(0) {
                vec![
                    CExpr::StringLit("Copied: %s\\n".to_string()),
                    CExpr::UIntLit(0),
                ]
            } else {
                vec![
                    CExpr::StringLit("Copied: %s\\n".to_string()),
                    CExpr::Deref(Box::new(CExpr::binary(
                        BinaryOp::Add,
                        CExpr::AddrOf(Box::new(CExpr::Var("stack_3e0".to_string()))),
                        CExpr::IntLit(312),
                    ))),
                ]
            },
            "expected imported stack-backed pointer input to stay stable, got {rendered:?}"
        );
    }

    #[test]
    fn modeled_internal_wrapper_result_is_repaired_like_imported_calls() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x2000, 3);
        ctx.state.analysis_ctx.ownership.call_ownership.insert(
            CallSiteId::from(source_call),
            CallOwnershipFact {
                source: CallSiteId::from(source_call),
                owner: Some(CallOwner {
                    visible_name: "buf".to_string(),
                    kind: CallOwnerKind::StableLocal,
                }),
                aliases: BTreeSet::from(["tmp:buf".to_string()]),
                direct_aliases: BTreeSet::new(),
                call_expr_keys: BTreeSet::new(),
            },
        );
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x401500,
            "helper.alloc_wrapper".to_string(),
        )])));
        ctx.inputs.callee_facts = Box::leak(Box::new(BTreeMap::from([(
            0x401500,
            CalleeFact {
                function_id: 0x401500,
                name: Some("helper.alloc_wrapper".to_string()),
                direct_callees: Vec::new(),
                callsite_count: 1,
                has_unknown_calls: false,
                arg_effects: BTreeMap::from([(
                    0,
                    CalleeArgEffect {
                        read: true,
                        write: false,
                        escape: false,
                        free: false,
                    },
                )]),
                memory_effects: Vec::new(),
                transfer_effects: Vec::new(),
                allocation_effects: Vec::new(),
                lifetime_effects: Vec::new(),
                sync_effects: Vec::new(),
                atomic_effects: Vec::new(),
                param_type_hints: BTreeMap::new(),
                return_type_hint: None,
                return_relation: CalleeReturnRelation::HeapAlloc,
                reads_global_memory: false,
                writes_global_memory: false,
                touches_unknown_memory: false,
            },
        )])));

        let rendered = ctx.render_call_arg_for_callee(
            &CExpr::Var("helper.alloc_wrapper".to_string()),
            result_call_arg(CExpr::Var("tmp:buf".to_string()), source_call, 0),
        );

        assert_eq!(
            rendered,
            CExpr::Var("buf".to_string()),
            "expected summary-modeled internal wrapper to preserve owned call result like an imported call, got {rendered:?}"
        );
    }

    #[test]
    fn prepared_call_site_root_resolves_copied_const_target_without_analysis() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });

        let prepared = prepared_from_r2il_blocks(&[entry], &arch).with_name("prepared_call_root");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.set_function_names(HashMap::from([(
            0x401050,
            "sym.function_name".to_string(),
        )]));
        ctx.inputs.symbols = Box::leak(Box::new(HashMap::from([(
            0x401050,
            "sym.symbol_name".to_string(),
        )])));
        ctx.inputs.callee_facts = Box::leak(Box::new(BTreeMap::from([(
            0x401050,
            minimal_callee_fact(0x401050, "sym.imp.fact_helper"),
        )])));

        let block = prepared.function().get_block(0x1000).expect("entry");
        let SSAOp::Call { target } = &block.ops[1] else {
            panic!("expected call op, got {:?}", block.ops[1]);
        };

        let call_view = ctx
            .prepared_call_view_for_site(block.addr, 1)
            .expect("prepared call view");
        let identity = call_view
            .callee_identity
            .as_ref()
            .expect("prepared call identity");
        assert_eq!(identity.display_name.as_deref(), Some("sym.imp.fact_helper"));
        assert_eq!(identity.primary_key(), "fact_helper");
        assert!(identity.aliases.contains("sym.function_name"));
        assert!(identity.aliases.contains("sym.symbol_name"));
        assert_eq!(call_view.callee_name.as_deref(), Some("sym.imp.fact_helper"));

        assert_eq!(
            ctx.resolve_call_target_for_site(block.addr, 1, target),
            CExpr::Var("sym.imp.fact_helper".to_string())
        );
        assert_eq!(
            ctx.call_target_identity(&CExpr::Var("const:401050".to_string())),
            Some("fact_helper".to_string())
        );
        assert!(
            ctx.is_imported_call_target(&CExpr::Var("const:401050".to_string())),
            "direct target identity should classify imported callee-fact names"
        );
        assert!(
            !ctx.is_modeled_call_target(&CExpr::Var("const:402000".to_string())),
            "unrelated direct targets must not inherit modeled status from existing callee facts"
        );
    }

    #[test]
    fn certified_prepared_call_args_require_argument_value_proof() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x10, 8),
            src: Varnode::constant(7, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });

        let prepared = prepared_from_r2il_blocks(&[entry], &arch).with_name("certified_call_arg");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));

        let block = prepared.function().get_block(0x1000).expect("entry");
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[2], block.addr, 2)
            .expect("call stmt");

        let CStmt::Expr(CExpr::Call { func, args }) = stmt else {
            panic!("expected certified call expression, got {stmt:?}");
        };
        assert_eq!(*func, CExpr::Var("sym.helper".to_string()));
        assert_eq!(args, vec![CExpr::IntLit(7)]);
    }

    #[test]
    fn prepared_call_arg_value_mismatch_residualizes() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x10, 8),
            src: Varnode::constant(7, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });

        let prepared =
            prepared_from_r2il_blocks(&[entry], &arch).with_name("mismatched_call_arg");
        let call_cert = prepared
            .callsite_certificate_for_op(0x1000, 2)
            .expect("callsite certificate");
        assert_ne!(
            call_cert.target, call_cert.argument_values[0],
            "target value should be a distinct wrong argument proof"
        );

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 2),
                crate::analysis::PreparedCallView {
                    direct_target: Some(0x401050),
                    callee_identity: None,
                    callee_name: Some("sym.helper".to_string()),
                    authoritative_args: vec![CExpr::IntLit(7)],
                    authoritative_arg_values: vec![call_cert.target],
                    result_owner: None,
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        let block = prepared.function().get_block(0x1000).expect("entry");
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[2], block.addr, 2)
            .expect("residual stmt");

        let CStmt::Comment(comment) = stmt else {
            panic!("expected residual comment, got {stmt:?}");
        };
        assert!(
            comment.contains("uncertified callsite arguments"),
            "unexpected residual comment: {comment}"
        );
    }

    #[test]
    fn synthesized_source_call_expr_requires_certified_argument_values() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x10, 8),
            src: Varnode::constant(7, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });

        let prepared =
            prepared_from_r2il_blocks(&[entry], &arch).with_name("certified_synth_source_call");
        let call_cert = prepared
            .callsite_certificate_for_op(0x1000, 2)
            .expect("callsite certificate");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 2),
                crate::analysis::PreparedCallView {
                    direct_target: Some(0x401050),
                    callee_identity: None,
                    callee_name: Some("sym.helper".to_string()),
                    authoritative_args: vec![CExpr::IntLit(7)],
                    authoritative_arg_values: vec![call_cert.target],
                    result_owner: None,
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        assert!(
            ctx.synthesized_call_expr_for_source_call((0x1000, 2))
                .is_none(),
            "synthesized source-call expressions must not reuse unproved prepared args"
        );
    }

    #[test]
    fn rendered_synthesized_source_call_records_callsite_proof() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x10, 8),
            src: Varnode::constant(7, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });

        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("certified_synth_rendered_call");
        let call_cert = prepared
            .callsite_certificate_for_op(0x1000, 2)
            .expect("callsite certificate");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 2),
                crate::analysis::PreparedCallView {
                    direct_target: Some(0x401050),
                    callee_identity: None,
                    callee_name: Some("sym.helper".to_string()),
                    authoritative_args: vec![CExpr::IntLit(7)],
                    authoritative_arg_values: vec![call_cert.argument_values[0]],
                    result_owner: None,
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        let call = ctx
            .synthesized_call_expr_for_source_call((0x1000, 2))
            .expect("certified synthesized call");
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert((0x1000, 2), call.clone());
        ctx.clear_effect_render_proofs();

        ctx.record_certified_call_render_proofs_for_stmt(&CStmt::Return(Some(call)))
            .expect("rendered call proof");

        let proofs = ctx.effect_render_proofs();
        assert_eq!(proofs.len(), 1, "expected one rendered call proof");
        assert_eq!(proofs[0].kind, EffectRenderProofKind::Call);
        assert_eq!((proofs[0].block_addr, proofs[0].op_idx), (0x1000, 2));
        assert_eq!(proofs[0].target, Some(call_cert.target));
        assert_eq!(proofs[0].values, vec![call_cert.argument_values[0]]);
    }

    #[test]
    fn certified_prepared_call_args_include_stack_home_certificate_values() {
        let arch = make_test_arch_x86_64();
        let stack_home = Varnode {
            space: SpaceId::Unique,
            offset: 0x1200,
            size: 8,
            meta: None,
        };
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntAdd {
            dst: stack_home.clone(),
            a: Varnode::register(0x28, 8),
            b: Varnode::constant(0x20, 8),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: stack_home,
            val: Varnode::constant(7, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::constant(0x401050, 8),
        });

        let prepared = prepared_from_r2il_blocks(&[entry], &arch).with_name("stack_home_call_arg");
        let call_cert = prepared
            .callsite_certificate_for_op(0x1000, 2)
            .expect("callsite certificate");
        assert_eq!(call_cert.stack_argument_values.len(), 1);
        assert_eq!(call_cert.argument_certificates.len(), 1);
        assert_eq!(
            call_cert.argument_certificates[0].value,
            call_cert.stack_argument_values[0].value
        );
        assert!(matches!(
            &call_cert.argument_certificates[0].location,
            r2ssa::CallArgumentLocation::Stack { .. }
        ));
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));

        let block = prepared.function().get_block(0x1000).expect("entry");
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[2], block.addr, 2)
            .expect("call stmt");

        let CStmt::Expr(CExpr::Call { func, args }) = stmt else {
            panic!("expected certified call expression, got {stmt:?}");
        };
        assert_eq!(*func, CExpr::Var("sym.helper".to_string()));
        assert_eq!(args, vec![CExpr::IntLit(7)]);
    }

    #[test]
    fn uncertified_prepared_call_args_render_residual_comment() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Call {
            target: Varnode::constant(0x401050, 8),
        });

        let prepared =
            prepared_from_r2il_blocks(&[entry], &arch).with_name("uncertified_call_arg");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 0),
                crate::analysis::PreparedCallView {
                    authoritative_args: vec![CExpr::Var("fake_arg".to_string())],
                    ..crate::analysis::PreparedCallView::default()
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        let block = prepared.function().get_block(0x1000).expect("entry");
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[0], block.addr, 0)
            .expect("residual stmt");

        let CStmt::Comment(comment) = stmt else {
            panic!("expected residual comment, got {stmt:?}");
        };
        assert!(
            comment.contains("uncertified callsite arguments"),
            "unexpected residual comment: {comment}"
        );
    }

    #[test]
    fn certified_materialized_phi_carriers_do_not_emit_residual_comments() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1810, 4);
        entry.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1818, 8),
        });

        let mut left = R2ILBlock::new(0x1814, 4);
        left.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(1, 8),
        });
        left.push(R2ILOp::Branch {
            target: Varnode::constant(0x181c, 8),
        });

        let mut right = R2ILBlock::new(0x1818, 4);
        right.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(2, 8),
        });
        right.push(R2ILOp::Branch {
            target: Varnode::constant(0x181c, 8),
        });

        let mut exit = R2ILBlock::new(0x181c, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let prepared =
            prepared_from_r2il_blocks(&[entry, left, right, exit], &arch).with_name("phi_carrier");
        let normalized = crate::normalize::materialize_phis(prepared.function());
        let fold_blocks = normalized.blocks().cloned().collect::<Vec<_>>();
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.analyze_blocks(&fold_blocks);

        let left_stmts = ctx.fold_block(
            normalized.get_block(0x1814).expect("left predecessor"),
            0x1814,
        );
        let right_stmts = ctx.fold_block(
            normalized.get_block(0x1818).expect("right predecessor"),
            0x1818,
        );
        let mut rendered = Vec::new();
        rendered.extend(left_stmts.iter().map(|stmt| format!("{stmt:?}")));
        rendered.extend(right_stmts.iter().map(|stmt| format!("{stmt:?}")));
        assert!(
            rendered
                .iter()
                .all(|stmt| !stmt.contains("r2sleigh residual:")),
            "materialized SSA phi carriers should stay cleanup candidates, got {rendered:?}"
        );
    }

    #[test]
    fn prepared_predicate_candidate_survives_without_legacy_flag_info() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntNotEqual {
            dst: Varnode::unique(1, 1),
            a: Varnode::register(0x10, 4),
            b: Varnode::constant(0, 4),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1008, 8),
            cond: Varnode::unique(1, 1),
        });
        let mut fallthrough = R2ILBlock::new(0x1004, 4);
        fallthrough.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut taken = R2ILBlock::new(0x1008, 4);
        taken.push(R2ILOp::Return {
            target: Varnode::constant(1, 8),
        });

        let prepared =
            prepared_from_r2il_blocks(&[entry, fallthrough, taken], &arch).with_name("pred");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let entry = prepared.function().get_block(0x1000).expect("entry");
        let SSAOp::CBranch { cond, .. } = &entry.ops[1] else {
            panic!("expected cbranch op, got {:?}", entry.ops[1]);
        };

        ctx.state.analysis_ctx.flag_info.compare_provenance.insert(
            cond.display_name(),
            crate::analysis::FlagCompareProvenance {
                lhs: "legacy_poison".to_string(),
                rhs: "1".to_string(),
                kind: crate::analysis::FlagCompareKind::Equality,
            },
        );

        assert_eq!(
            ctx.extract_condition_from_block(entry),
            Some(CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("arg1".to_string()),
                CExpr::IntLit(0),
            ))
        );
        assert_eq!(
            ctx.predicate_candidate_for_var(cond),
            Some(CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("arg1".to_string()),
                CExpr::IntLit(0),
            ))
        );
    }

    #[test]
    fn prepared_predicate_alias_cycle_returns_stable_var_instead_of_recursing() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            owner_expr_by_name: HashMap::from([
                ("tmp:pred.1".to_string(), CExpr::Var("tmp:pred.2".to_string())),
                ("tmp:pred.2".to_string(), CExpr::Var("tmp:pred.1".to_string())),
            ]),
            ..PreparedSemanticView::default()
        })));

        let mut visited = HashSet::new();
        let resolved = ctx.resolve_predicate_operand(
            &CExpr::Var("tmp:pred.1".to_string()),
            0,
            &mut visited,
        );

        assert_eq!(resolved, CExpr::Var("tmp:pred.1".to_string()));
    }

    #[test]
    fn prepared_empty_call_view_args_fall_back_to_analyzed_call_args() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 1),
                crate::analysis::PreparedCallView {
                    authoritative_args: Vec::new(),
                    ..crate::analysis::PreparedCallView::default()
                },
            )]),
            ..PreparedSemanticView::default()
        })));
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 1),
            vec![crate::analysis::CallArgBinding::input(
                crate::analysis::SemanticCallArg::FallbackExpr(CExpr::Var("len".to_string())),
            )],
        );

        assert_eq!(
            ctx.render_authoritative_source_args_for_call((0x1000, 1)),
            vec![CExpr::Var("len".to_string())]
        );
    }

    #[test]
    fn return_inline_ssa_storage_carriers_inline_raw_tmp_and_const() {
        let mut ctx = make_x86_64_ctx();
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "tmp:ret_1".to_string(),
            CExpr::binary(
                BinaryOp::BitXor,
                CExpr::Var("value".to_string()),
                CExpr::IntLit(1),
            ),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("const:1_0".to_string(), CExpr::IntLit(1));

        assert_eq!(
            ctx.resolve_return_candidate(&CExpr::Var("tmp:ret_1".to_string())),
            CExpr::binary(
                BinaryOp::BitXor,
                CExpr::Var("value".to_string()),
                CExpr::IntLit(1)
            )
        );
        assert_eq!(
            ctx.resolve_return_candidate(&CExpr::Var("const:1_0".to_string())),
            CExpr::IntLit(1)
        );
    }

    #[test]
    fn return_inline_ssa_storage_carriers_require_raw_or_mapped_alias() {
        let mut unmapped = make_x86_64_ctx();
        unmapped
            .state
            .analysis_ctx
            .use_info
            .definitions
            .insert("tmp:3e480_1".to_string(), CExpr::IntLit(7));

        assert_eq!(
            unmapped.expand_return_expr(
                &CExpr::Var("value_3e480".to_string()),
                0,
                &mut HashSet::new()
            ),
            CExpr::Var("value_3e480".to_string())
        );
        assert_eq!(
            unmapped.expand_return_expr(
                &CExpr::Var("t42_1".to_string()),
                0,
                &mut HashSet::new()
            ),
            CExpr::Var("t42_1".to_string())
        );
        unmapped
            .state
            .analysis_ctx
            .use_info
            .definitions
            .insert("ordinary_alias".to_string(), CExpr::IntLit(9));
        assert_eq!(
            unmapped.expand_return_expr(
                &CExpr::Var("ordinary_alias".to_string()),
                0,
                &mut HashSet::new()
            ),
            CExpr::Var("ordinary_alias".to_string())
        );

        let mut mapped = make_x86_64_ctx();
        mapped
            .state
            .analysis_ctx
            .use_info
            .definitions
            .insert("tmp:3e480_1".to_string(), CExpr::IntLit(7));
        mapped
            .state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert("tmp:3e480_1".to_string(), "value_3e480".to_string());

        assert_eq!(
            mapped.expand_return_expr(
                &CExpr::Var("value_3e480".to_string()),
                0,
                &mut HashSet::new()
            ),
            CExpr::IntLit(7)
        );
    }

    #[test]
    fn prepared_imported_arg_rewrite_canonicalizes_stack_home_aliases() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([(
            "rdi".to_string(),
            "s".to_string(),
        )])));
        ctx.state
            .analysis_ctx
            .stack_info
            .stack_vars
            .insert(-24, "s_home".to_string());
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            stack_aliases_by_offset: BTreeMap::from([(
                -24,
                crate::analysis::prepared_semantic::StackAliasView {
                    visible_name: "s_home".to_string(),
                    arg_alias: Some("s".to_string()),
                    binding_kind: Some(VisibleBindingKind::HiddenHome),
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        assert_eq!(
            ctx.normalize_imported_call_arg_expr(
                CExpr::Var("s_home".to_string()),
                true,
                false,
                false,
            ),
            CExpr::Var("s".to_string())
        );
    }

    #[test]
    fn final_public_predicate_sanitizer_hides_raw_tmp_names() {
        let ctx = make_x86_64_ctx();
        let normalized = ctx.normalize_final_stmt_calls(CStmt::if_stmt(
            CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("tmp:3e480".to_string()),
                CExpr::IntLit(2018),
            ),
            CStmt::Empty,
            None,
        ));

        let CStmt::If { cond, .. } = normalized else {
            panic!("expected if statement");
        };
        assert_eq!(
            cond,
            CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("value_3e480".to_string()),
                CExpr::IntLit(2018),
            )
        );
    }

    #[test]
    fn final_public_call_arg_sanitizer_does_not_certify_raw_stack_placeholders() {
        let ctx = make_x86_64_ctx();
        let normalized = ctx.normalize_final_stmt_calls(CStmt::Expr(CExpr::call(
            CExpr::Var("sym.rpl_mbrtoc32".to_string()),
            vec![CExpr::binary(
                BinaryOp::Add,
                CExpr::IntLit(12),
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::Var("var_8h".to_string()),
                    CExpr::IntLit(48),
                ),
            )],
        )));

        let CStmt::Expr(CExpr::Call { args, .. }) = normalized else {
            panic!("expected call statement");
        };
        let mut names = Vec::new();
        args[0].visit(&mut |expr| {
            if let CExpr::Var(name) = expr {
                names.push(name.clone());
            }
        });
        assert!(
            names.iter().all(|name| name != "slot_8"),
            "uncertified stack placeholder must not become a canonical slot: {args:?}"
        );
        assert!(
            names.iter().any(|name| name == "var_8h"),
            "uncertified stack placeholder should remain visibly uncertified: {args:?}"
        );
    }

    #[test]
    fn prepared_imported_scalar_expr_uses_precomputed_owner_aliases() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            owner_expr_by_name: HashMap::from([(
                "tmp:size_1".to_string(),
                CExpr::Var("len".to_string()),
            )]),
            ..PreparedSemanticView::default()
        })));

        assert_eq!(
            ctx.prepared_imported_semantic_arg_expr(
                &crate::analysis::SemanticValue::Scalar(ScalarValue::Expr(CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("tmp:size_1".to_string()),
                    CExpr::IntLit(1),
                ))),
                false,
            ),
            Some(CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("len".to_string()),
                CExpr::IntLit(1),
            ))
        );
    }

    #[test]
    fn prepared_generic_zero_compare_yields_to_local_compare_recovery() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            branch_predicate_expr_by_block: BTreeMap::from([(
                0x1000,
                CExpr::binary(
                    BinaryOp::Ne,
                    CExpr::Var("var_8h".to_string()),
                    CExpr::IntLit(0),
                ),
            )]),
            ..PreparedSemanticView::default()
        })));

        let block = make_block(vec![
            SSAOp::IntNotEqual {
                dst: make_var("ZF", 3, 1),
                a: make_var("arg1", 0, 4),
                b: make_var("arg2", 0, 4),
            },
            SSAOp::CBranch {
                target: make_var("ram:1008", 0, 8),
                cond: make_var("ZF", 3, 1),
            },
        ]);

        assert_eq!(
            ctx.extract_condition_from_block(&block),
            Some(CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("arg1".to_string()),
                CExpr::Var("arg2".to_string()),
            ))
        );
    }

    #[test]
    fn prepared_generic_arithmetic_compare_yields_to_local_compare_recovery() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            branch_predicate_expr_by_block: BTreeMap::from([(
                0x1000,
                CExpr::binary(
                    BinaryOp::Ne,
                    CExpr::binary(
                        BinaryOp::Add,
                        CExpr::Var("var_8h".to_string()),
                        CExpr::Var("var_8h".to_string()),
                    ),
                    CExpr::IntLit(100),
                ),
            )]),
            ..PreparedSemanticView::default()
        })));

        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: make_var("tmp:sum", 1, 4),
                a: make_var("arg1", 0, 4),
                b: make_var("arg1", 0, 4),
            },
            SSAOp::IntNotEqual {
                dst: make_var("ZF", 3, 1),
                a: make_var("tmp:sum", 1, 4),
                b: make_var("const:64", 0, 4),
            },
            SSAOp::CBranch {
                target: make_var("ram:1008", 0, 8),
                cond: make_var("ZF", 3, 1),
            },
        ]);

        assert_eq!(
            ctx.extract_condition_from_block(&block),
            Some(CExpr::binary(
                BinaryOp::Ne,
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("arg1".to_string()),
                    CExpr::Var("arg1".to_string()),
                ),
                CExpr::IntLit(100),
            ))
        );
    }

    #[test]
    fn prepared_memory_load_uses_named_global_object_without_analysis_state() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x404000, 8),
        });
        entry.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(1, 8),
        });

        let prepared = prepared_from_r2il_blocks(&[entry], &arch).with_name("prepared_global_load");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.inputs.symbols = Box::leak(Box::new(HashMap::from([(
            0x404000,
            "obj.global_value".to_string(),
        )])));

        let block = prepared.function().get_block(0x1000).expect("entry");
        ctx.current_block_addr.set(Some(block.addr));
        ctx.current_op_idx.set(Some(1));
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[1], block.addr, 1)
            .expect("load stmt");
        ctx.current_block_addr.set(None);
        ctx.current_op_idx.set(None);

        let CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            right,
            ..
        }) = stmt
        else {
            panic!("expected assignment stmt, got {stmt:?}");
        };
        assert_eq!(*right, CExpr::Var("obj.global_value".to_string()));
    }

    #[test]
    fn prepared_analyze_blocks_builds_stack_info_from_visible_bindings() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntSub {
            dst: Varnode::unique(1, 8),
            a: Varnode::register(0x20, 8),
            b: Varnode::constant(8, 8),
        });
        entry.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(1, 8),
        });

        let prepared = prepared_from_r2il_blocks(&[entry], &arch).with_name("prepared_stack");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.set_external_stack_vars(HashMap::from([(
            -8,
            stack_var_spec("buf", Some(crate::CType::Int(32)), Some("rbp")),
        )]));

        let blocks = prepared.function().blocks().cloned().collect::<Vec<_>>();
        ctx.analyze_blocks(&blocks);

        assert_eq!(ctx.stack_vars_map().get(&-8), Some(&"buf".to_string()));
        assert_eq!(ctx.resolve_stack_var(-8), Some("buf".to_string()));
    }

    #[test]
    fn prepared_analyze_blocks_marks_flag_only_values_without_legacy_flag_analysis() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntNotEqual {
            dst: Varnode::unique(1, 1),
            a: Varnode::register(0x10, 4),
            b: Varnode::constant(0, 4),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1008, 8),
            cond: Varnode::unique(1, 1),
        });
        let mut fallthrough = R2ILBlock::new(0x1004, 4);
        fallthrough.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut taken = R2ILBlock::new(0x1008, 4);
        taken.push(R2ILOp::Return {
            target: Varnode::constant(1, 8),
        });

        let prepared =
            prepared_from_r2il_blocks(&[entry, fallthrough, taken], &arch).with_name("pred_flags");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let blocks = prepared.function().blocks().cloned().collect::<Vec<_>>();
        let entry = prepared.function().get_block(0x1000).expect("entry");
        let SSAOp::CBranch { cond, .. } = &entry.ops[1] else {
            panic!("expected cbranch op, got {:?}", entry.ops[1]);
        };

        ctx.analyze_blocks(&blocks);

        assert!(ctx.flag_only_values_set().contains(&cond.display_name()));
        assert_eq!(
            ctx.extract_condition_from_block(entry),
            Some(CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("arg1".to_string()),
                CExpr::IntLit(0),
            ))
        );
    }

    #[test]
    fn prepared_predicate_candidate_for_branch_block_uses_block_assumptions_fallback() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x5000, 4);
        entry.push(R2ILOp::IntEqual {
            dst: Varnode::unique(1, 1),
            a: Varnode::register(0x00, 8),
            b: Varnode::register(0x18, 8),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x5008, 8),
            cond: Varnode::unique(1, 1),
        });
        let mut fallthrough = R2ILBlock::new(0x5004, 4);
        fallthrough.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut taken = R2ILBlock::new(0x5008, 4);
        taken.push(R2ILOp::Return {
            target: Varnode::constant(1, 8),
        });

        let prepared = prepared_from_r2il_blocks(&[entry, fallthrough, taken], &arch)
            .with_name("branch_assumption");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let cond = make_var("tmp:pred", 1, 1);
        let lhs_value_id = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.name.eq_ignore_ascii_case("rax") && value.var.version == 0)
            .map(|value| value.id)
            .expect("lhs value id");
        let rhs_value_id = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.name.eq_ignore_ascii_case("rsi") && value.var.version == 0)
            .map(|value| value.id)
            .expect("rhs value id");
        let cond_value_id = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.is_temp())
            .map(|value| value.id)
            .expect("cond value id");
        let mut predicate_facts = r2ssa::PredicateFacts::default();
        predicate_facts.predicates.insert(
            r2ssa::PredicateId(1),
            r2ssa::PredicateFact {
                id: r2ssa::PredicateId(1),
                block_addr: 0x5000,
                condition: lhs_value_id,
                comparison: Some(r2ssa::CompareProvenance {
                    kind: r2ssa::CompareKind::Equal,
                    lhs: lhs_value_id,
                    rhs: rhs_value_id,
                }),
                true_target: 0x5008,
                false_target: 0x5004,
            },
        );
        predicate_facts.block_assumptions.insert(
            0x5000,
            vec![r2ssa::BlockAssumption {
                predecessor: 0x5000,
                predicate: r2ssa::PredicateId(1),
                truth: true,
            }],
        );
        ctx.inputs.prepared_predicates = Some(Box::leak(Box::new(predicate_facts)));

        assert_ne!(
            lhs_value_id, cond_value_id,
            "test setup must force the direct predicate match to miss"
        );
        assert!(
            matches!(
                ctx.prepared_predicate_candidate_for_branch_block_for_test(0x5000, &cond),
                Some(CExpr::Binary {
                    op: BinaryOp::Eq,
                    ..
                })
            ),
            "expected block_assumptions fallback to recover a compare expression"
        );
    }
}
