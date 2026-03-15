#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{HashMap, HashSet};

    use crate::{
        FoldArchConfig,
        FoldInputs,
        analysis::{PassEnv, StackInfo, UseInfo},
    };
    use r2il::{R2ILBlock, R2ILOp, Varnode};
    use r2types::{
        ExternalField, ExternalStackVarSpec, ExternalStruct, ExternalTypeDb, FunctionParamSpec,
        FunctionSignatureSpec, FunctionTypeFacts, Signedness, SolvedTypes,
        SolverDiagnostics, StructShape, TypeArena, TypeId, TypeOracle,
    };

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
                params: value
                    .params
                    .iter()
                    .map(crate::ctype_to_type_like)
                    .collect(),
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
            base: base.map(str::to_string),
        }
    }

    fn signature_spec(ret: Option<CType>, params: Vec<(&str, Option<CType>)>) -> FunctionSignatureSpec {
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
        let empty_str = Box::leak(Box::new(HashMap::new()));
        let empty_fn = Box::leak(Box::new(HashMap::new()));
        let empty_ty = Box::leak(Box::new(HashMap::new()));
        FoldingContext::from_inputs(FoldInputs {
            arch,
            function_names: empty_u64,
            strings: empty_u64,
            symbols: empty_u64,
            known_function_signatures: empty_fn,
            external_stack_vars: empty_stack,
            external_type_db: Box::leak(Box::new(r2types::ExternalTypeDb::default())),
            param_register_aliases: empty_str,
            type_hints: empty_ty,
            type_oracle: None,
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
        let empty_str = Box::leak(Box::new(HashMap::new()));
        let empty_fn = Box::leak(Box::new(HashMap::new()));
        let empty_ty = Box::leak(Box::new(HashMap::new()));
        FoldingContext::from_inputs(FoldInputs {
            arch,
            function_names: empty_u64,
            strings: empty_u64,
            symbols: empty_u64,
            known_function_signatures: empty_fn,
            external_stack_vars: empty_stack,
            external_type_db: Box::leak(Box::new(r2types::ExternalTypeDb::default())),
            param_register_aliases: empty_str,
            type_hints: empty_ty,
            type_oracle: None,
        })
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
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            format_addr,
            format.to_string(),
        )])));
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
                expr_contains_var(func, target) || args.iter().any(|arg| expr_contains_var(arg, target))
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
                        .is_some_and(|(reg, _)| !reg.is_empty() && reg.chars().all(|c| c.is_ascii_digit()))
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
        assert_eq!(parse_const_value("const:42"), Some(42));
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
                CExpr::Binary { op: BinaryOp::Add, left, right } => {
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
            CExpr::binary(BinaryOp::Add, CExpr::UIntLit(0x402000), CExpr::IntLit(0x29e)),
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
            CExpr::binary(BinaryOp::Add, CExpr::UIntLit(0x402000), CExpr::IntLit(0x29e)),
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
        assert_eq!(args[0], CExpr::StringLit("unlock(%d, %d, %d) = %d\\n".to_string()));
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
            args.iter().skip(1).all(|arg| !expr_contains_transient_call_artifact(arg)),
            "unlock printf should keep only recovered locals/helper result, got {args:?}"
        );
    }

    #[test]
    fn test_imported_printf_result_slot_rebuilds_solve_equation_call_from_authoritative_source_bindings(
    ) {
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
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x2000, 0),
            vec![stack_load_call_arg(-92, 4)],
        );
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
            args.iter().skip(1).all(|arg| !expr_contains_transient_call_artifact(arg)),
            "solve_equation printf should keep recovered local/helper result, got {args:?}"
        );
    }

    #[test]
    fn test_imported_printf_result_slot_rebuilds_complex_check_call_from_authoritative_source_bindings(
    ) {
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
        assert_eq!(args[0], CExpr::StringLit("complex_check(%d, %d) = %d\\n".to_string()));
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
            args.iter().skip(1).all(|arg| !expr_contains_transient_call_artifact(arg)),
            "complex_check printf should keep recovered locals/helper result, got {args:?}"
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
        ctx.state.analysis_ctx.use_info.var_aliases.insert(
            "tmp:fmt_1".to_string(),
            "t19".to_string(),
        );
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
        assert_eq!(args[0], CExpr::StringLit("usage: vuln_test <n>\\n".to_string()));
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
        assert!(ctx.should_inline(&t0.display_name()));
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
        assert!(ctx.should_inline(&t0.display_name()));
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
        ctx.state.analysis_ctx.use_info.definitions.insert(
            real_index.display_name(),
            CExpr::Var("local_c".to_string()),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            real_index.display_name(),
            crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Expr(
                CExpr::Var("local_c".to_string()),
            )),
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
    fn test_member_access_uses_subscript_base_when_base_has_generic_ptr_arith_definition() {
        let idx = make_var("arg2", 0, 4);
        let base = make_var("tmp:9400", 1, 8);
        let addr = make_var("tmp:9401", 1, 8);
        let dst = make_var("tmp:9402", 1, 4);
        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.use_info.ptr_members.insert(
            addr.display_name(),
            (base.clone(), 8),
        );
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
        let crate::analysis::SemanticValue::Load { addr, .. } = semantic
        else {
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
    fn test_member_access_reconstructs_combined_struct_array_index_scale() {
        let base = make_var("tmp:9600", 1, 8);
        let addr = make_var("tmp:9601", 1, 8);
        let dst = make_var("tmp:9602", 1, 4);
        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.use_info.ptr_members.insert(
            addr.display_name(),
            (base.clone(), 8),
        );
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
        ctx.state
            .analysis_ctx
            .use_info
            .type_hints
            .insert("arr".to_string(), CType::ptr(CType::Struct("DemoStruct".to_string())));
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
        let crate::analysis::SemanticValue::Load { addr, .. } = semantic
        else {
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
            [("x0".to_string(), "arg1".to_string()), ("x1".to_string(), "arg2".to_string())]
                .into_iter()
                .collect(),
        ));
        ctx.set_type_hints(
            [
                ("arg1".to_string(), CType::ptr(CType::Struct("DemoStruct".to_string()))),
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
            matches!(
                rendered,
                CExpr::Member { .. } | CExpr::PtrMember { .. }
            ),
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
            [("x0".to_string(), "arg1".to_string()), ("x1".to_string(), "arg2".to_string())]
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
    fn test_render_memory_access_from_visible_expr_recovers_indexed_member_from_raw_pointer_math() {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.param_register_aliases = Box::leak(Box::new(
            [("x0".to_string(), "arg1".to_string()), ("x1".to_string(), "arg2".to_string())]
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
        assert!(shape.index.is_some(), "expected recovered index, got {shape:?}");

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
            matches!(direct_visible, CExpr::Member { .. } | CExpr::PtrMember { .. }),
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
            [("x0".to_string(), "arg1".to_string()), ("x1".to_string(), "arg2".to_string())]
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
                CExpr::Var("0xdead".to_string())
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
                CExpr::Var("0xffffffff".to_string())
            )
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
            stack_var_spec("buf", Some(CType::Array(Box::new(CType::Int(8)), Some(64))), Some("RBP")),
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
        external.insert(
            -64,
            stack_var_spec("buf", None, Some("RBP")),
        );
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
        external.insert(
            -64,
            stack_var_spec("buf", None, Some("RBP")),
        );
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
                CExpr::IntLit(19),
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
            CExpr::binary(BinaryOp::Add, CExpr::UIntLit(0x100002000), CExpr::IntLit(0x638)),
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
    fn test_lookup_definition_prefers_forwarded_semantic_value_over_register_artifact() {
        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "tmp:ret_1".to_string(),
            CExpr::Var("rax_2".to_string()),
        );
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "src_1".to_string(),
            CExpr::Var("arg1".to_string()),
        );
        ctx.state.analysis_ctx.use_info.forwarded_values.insert(
            "tmp:ret_1".to_string(),
            crate::analysis::ValueProvenance {
                source: "src_1".to_string(),
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
                CExpr::binary(
                    BinaryOp::Lt,
                    CExpr::Var("sp".to_string()),
                    CExpr::IntLit(0),
                ),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Var("tmpzr_1".to_string()),
                CExpr::binary(
                    BinaryOp::Eq,
                    CExpr::Var("sp".to_string()),
                    CExpr::IntLit(0),
                ),
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
        let ne = ctx.simplify_condition_expr(CExpr::unary(
            UnaryOp::Not,
            CExpr::Var("zf_7".to_string()),
        ));

        assert_eq!(
            eq,
            CExpr::binary(BinaryOp::Eq, CExpr::Var("result".to_string()), CExpr::IntLit(25))
        );
        assert_eq!(
            ne,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("result".to_string()), CExpr::IntLit(25))
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
        let ge = ctx.simplify_condition_expr(CExpr::unary(
            UnaryOp::Not,
            CExpr::Var("cf_1".to_string()),
        ));
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
            CExpr::binary(BinaryOp::Ne, CExpr::Var("arg1".to_string()), CExpr::IntLit(25))
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
        assert_eq!(
            cond,
            CExpr::binary(
                BinaryOp::Ne,
                CExpr::Var("rax_1".to_string()),
                CExpr::IntLit(0),
            )
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
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[
            entry,
            early_return,
            scalar_path,
            final_exit,
        ])
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
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "resolved_1".to_string(),
            CExpr::Var("arg1".to_string()),
        );
        ctx.state.analysis_ctx.use_info.forwarded_values.insert(
            ret.display_name(),
            crate::analysis::ValueProvenance {
                source: "resolved_1".to_string(),
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
    fn test_return_register_write_keeps_semantic_indexed_load_shape() {
        let idx_src = make_var("ESI", 0, 4);
        let arr_src = make_var("RDI", 0, 8);
        let eax = make_var("EAX", 2, 4);
        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.use_info.type_hints.insert(
            arr_src.display_name(),
            CType::ptr(CType::Int(32)),
        );
        ctx.state.analysis_ctx.use_info.type_hints.insert(
            idx_src.display_name(),
            CType::Int(32),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            eax.display_name(),
            crate::analysis::SemanticValue::Load {
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(
                        arr_src,
                    )),
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
    fn test_get_return_expr_keeps_both_semantic_member_loads_in_sum() {
        let base = make_var("RDI", 0, 8);
        let idx = make_var("ESI", 0, 4);
        let load_first = make_var("EAX", 1, 4);
        let load_second = make_var("tmp:11f00", 8, 4);
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
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(base.clone())),
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
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(base.clone())),
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
            matches!(expr, CExpr::Binary { op: BinaryOp::Add, .. }),
            "expected semantic return to stay a sum, got {expr:?}"
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
            SSAOp::Copy { dst: ret.clone(), src: load },
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
        let base_norm = ctx.debug_normalized_addr_from_visible_expr(&CExpr::Var("arg1".to_string()));
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
    fn test_observed_live_arm64_struct_field_store_does_not_reinterpret_stack_slot_as_member_zero() {
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
            target: Varnode::constant(0x1028, 8),
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
            target: Varnode::constant(0x1028, 8),
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
        let type_hints = HashMap::from([(
            "argv".to_string(),
            CType::ptr(CType::ptr(CType::Int(8))),
        )]);
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

        let function_names =
            HashMap::from([(0x1000025d8, "sym.imp.atoi".to_string())]);
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
        assert_eq!(args.len(), 2, "expected printf format + argv[0], got {args:?}");
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
        let (root, raw, semanticized) =
            ctx.debug_return_expr_stages(&make_var("tmp:20380", 1, 4));
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
        assert_eq!(
            ctx.state.analysis_ctx.use_info.definitions.get("X0_2"),
            Some(&CExpr::call(
                CExpr::Var("sym._unlock".to_string()),
                vec![CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]
            )),
            "expected helper return register to bind to the helper call expression"
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
                    && args == &vec![CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]
            ),
            "expected printf call args to preserve the helper result expression, got {printf_call_args:?}"
        );
        let stmts = ctx.fold_block(&block, block.addr);
        assert_eq!(stmts.len(), 1, "expected helper call to inline into the printf use, got {stmts:?}");

        let CStmt::Expr(CExpr::Call { func, args }) = &stmts[0] else {
            panic!("expected folded printf call, got {stmts:?}");
        };
        assert_eq!(**func, CExpr::Var("sym.imp.printf".to_string()));
        assert_eq!(
            args.first(),
            Some(&CExpr::StringLit("unlock(%d, %d, %d) = %d\\n".to_string()))
        );
        assert_eq!(&args[1..4], &[CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]);
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
            args.iter().skip(1).all(|arg| !expr_contains_transient_call_artifact(arg)),
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
        assert_eq!(&args[1..4], &[CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]);
        assert_eq!(**helper_func, CExpr::Var("sym._unlock".to_string()));
        assert_eq!(
            helper_args,
            &vec![CExpr::IntLit(1), CExpr::IntLit(2), CExpr::IntLit(3)]
        );
        assert!(
            args.iter().skip(1).all(|arg| !expr_contains_transient_call_artifact(arg)),
            "post-call helper recovery must keep preserved inputs clean, got {args:?}"
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
            (-44, stack_var_spec("local_2c", Some(CType::Int(32)), Some("x29"))),
            (-48, stack_var_spec("local_30", Some(CType::Int(32)), Some("x29"))),
            (-52, stack_var_spec("local_34", Some(CType::Int(32)), Some("x29"))),
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
            args.iter().skip(1).all(|arg| !expr_contains_transient_call_artifact(arg)),
            "live-shaped unlock printf args should not regress to transient artifacts, got {args:?}"
        );
    }

    #[test]
    fn folded_arm64_printf_live_unlock_shape_with_prior_atoi_keeps_result_slot_owned() {
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
            (-44, stack_var_spec("local_2c", Some(CType::Int(32)), Some("x29"))),
            (-48, stack_var_spec("local_30", Some(CType::Int(32)), Some("x29"))),
            (-52, stack_var_spec("local_34", Some(CType::Int(32)), Some("x29"))),
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
        let Some(CStmt::Expr(CExpr::Call { args, .. })) = stmts.iter().find(|stmt| matches!(
            stmt,
            CStmt::Expr(CExpr::Call { func, .. })
                if **func == CExpr::Var("sym.imp.printf".to_string())
        )) else {
            panic!("expected folded printf call, got {stmts:?}");
        };
        assert_eq!(args[0], CExpr::StringLit("unlock(%d, %d, %d) = %d\\n".to_string()));
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
            args.iter().skip(1).all(|arg| !expr_contains_transient_call_artifact(arg)),
            "live unlock printf with prior atoi should not regress to transient artifacts, got {args:?}"
        );
    }

    #[test]
    fn folded_arm64_printf_live_unlock_shape_direct_result_store_keeps_result_slot_owned() {
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
            (-44, stack_var_spec("local_2c", Some(CType::Int(32)), Some("x29"))),
            (-48, stack_var_spec("local_30", Some(CType::Int(32)), Some("x29"))),
            (-52, stack_var_spec("local_34", Some(CType::Int(32)), Some("x29"))),
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
        assert_eq!(args[0], CExpr::StringLit("unlock(%d, %d, %d) = %d\\n".to_string()));
        assert_eq!(args[1], CExpr::Var("local_2c".to_string()));
        assert_eq!(args[2], CExpr::Var("local_30".to_string()));
        assert_eq!(args[3], CExpr::Var("local_34".to_string()));
        assert!(
            matches!(
                &args[4],
                CExpr::Call { func, args }
                    if **func == CExpr::Var("sym._unlock".to_string())
                        && args
                            == &vec![
                                CExpr::Var("local_2c".to_string()),
                                CExpr::Var("local_30".to_string()),
                                CExpr::Var("local_34".to_string()),
                            ]
            ),
            "expected final printf arg to be helper result call, got {args:?}"
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
                b: make_var("const:64", 0, 4),
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
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(crate::CType::Int(64)),
                vec![
                    ("arg1", Some(crate::CType::Int(32))),
                    ("arg2", Some(crate::CType::Int(32))),
                ],
            )),
            external_stack_vars: HashMap::from([(
                -4,
                stack_var_spec("var_4h", Some(crate::CType::Int(32)), Some("RBP")),
            )]),
            ..FunctionTypeFacts::default()
        });

        let output = decompiler.decompile(&func);
        assert!(
            output.contains("int64_t sym._complex_check(int32_t arg1, int32_t arg2)"),
            "expected stable x86 header, got:\n{output}"
        );
        assert!(
            output.contains("var_4h = 0;") && output.contains("var_4h = 1;"),
            "expected named local carrier assignments, got:\n{output}"
        );
        assert!(
            output.contains("return 0;") && output.contains("return 1;"),
            "expected concrete branch returns, got:\n{output}"
        );
        assert!(!output.contains("{\n    }\n"), "unexpected empty if body in:\n{output}");
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
        assert_eq!(
            cond,
            CExpr::binary(
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
                CExpr::IntLit(19),
            )
        );

        let mut decompiler = crate::Decompiler::new(crate::DecompilerConfig::x86_64());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(crate::CType::Int(64)),
                vec![("arg1", Some(crate::CType::Int(32)))],
            )),
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
            output.contains("if ((arg1 << 1) + 5 != 19)"),
            "expected arg-backed scalar condition, got:\n{output}"
        );
        assert!(
            !output.contains("*(rbp"),
            "unexpected raw frame deref in:\n{output}"
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
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(crate::CType::Int(64)),
                vec![
                    ("arg1", Some(crate::CType::Int(32))),
                    ("arg2", Some(crate::CType::Int(32))),
                ],
            )),
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
                sources: vec![(0x10000107a, make_var("EAX", 0, 4)), (0x100001082, make_var("EAX", 0, 4))],
            },
            PhiNode {
                dst: make_var("RAX", 6, 8),
                sources: vec![(0x10000107a, make_var("RAX", 0, 8)), (0x100001082, make_var("RAX", 0, 8))],
            },
            PhiNode {
                dst: make_var("tmp:11f00", 5, 4),
                sources: vec![(0x10000107a, make_var("tmp:11f00", 0, 4)), (0x100001082, make_var("tmp:11f00", 0, 4))],
            },
            PhiNode {
                dst: make_var("tmp:4700", 13, 8),
                sources: vec![(0x10000107a, make_var("tmp:4700", 0, 8)), (0x100001082, make_var("tmp:4700", 0, 8))],
            },
            PhiNode {
                dst: make_var("tmp:6a80", 7, 4),
                sources: vec![(0x10000107a, make_var("tmp:6a80", 0, 4)), (0x100001082, make_var("tmp:6a80", 0, 4))],
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
        assert_eq!(then_stmts, vec![CStmt::Return(Some(CExpr::Var("arg1".to_string())))]);
        assert_eq!(else_stmts, vec![CStmt::Return(Some(CExpr::Var("arg2".to_string())))]);

        let mut decompiler = crate::Decompiler::new(crate::DecompilerConfig::x86_64());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(crate::CType::Int(64)),
                vec![
                    ("arg1", Some(crate::CType::Int(32))),
                    ("arg2", Some(crate::CType::Int(32))),
                ],
            )),
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
            output.contains("int64_t sym._test_bool_carrier_chain_fixture_shape(int32_t arg1, int32_t arg2)"),
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
    fn folded_x86_printf_result_slot_recovers_helper_call_from_eax_alias() {
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
    fn imported_printf_stack_backed_pointer_arg_without_named_positive_base_renders_visible_storage() {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x1000_1000,
            "Copied: %s\\n".to_string(),
        )])));

        let rendered = ctx.render_call_args_for_callee(
            &CExpr::Var("sym.imp.printf".to_string()),
            vec![
                crate::analysis::CallArgBinding::input(crate::analysis::SemanticCallArg::StringAddr(
                    0x1000_1000,
                )),
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::semantic(
                        crate::analysis::SemanticValue::Load {
                            addr: crate::analysis::NormalizedAddr {
                                base: crate::analysis::BaseRef::StackSlot(0x3e0),
                                index: None,
                                scale_bytes: 0,
                                offset_bytes: 312,
                            },
                            size: 8,
                        },
                    ),
                ),
            ],
        );

        assert_eq!(
            rendered,
            vec![
                CExpr::StringLit("Copied: %s\\n".to_string()),
                CExpr::Deref(Box::new(CExpr::binary(
                    BinaryOp::Add,
                    CExpr::AddrOf(Box::new(CExpr::Var("stack_3e0".to_string()))),
                    CExpr::IntLit(312),
                ))),
            ],
            "expected imported stack-backed pointer input to preserve visible storage identity instead of collapsing to 0U"
        );
    }

}
