use super::calls::CertifiedCallArgs;
use super::*;

impl<'a> FoldingContext<'a> {
    pub(super) fn lowered_from_stmt(stmt: CStmt) -> LoweredOp {
        match stmt {
            CStmt::Expr(CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                right,
            }) => LoweredOp::Assign {
                lhs: *left,
                rhs: *right,
            },
            CStmt::Expr(expr) => LoweredOp::Expr(expr),
            CStmt::Return(expr) => LoweredOp::Return(expr),
            CStmt::Comment(text) => LoweredOp::Comment(text),
            CStmt::Empty => LoweredOp::None,
            _ => LoweredOp::None,
        }
    }

    pub(super) fn lowered_to_stmt(&self, lowered: LoweredOp) -> Option<CStmt> {
        match lowered {
            LoweredOp::Assign { lhs, rhs } => self.assign_stmt(lhs, rhs),
            LoweredOp::Expr(expr) => Some(CStmt::Expr(expr)),
            LoweredOp::Return(expr) => Some(CStmt::Return(expr)),
            LoweredOp::Comment(text) => Some(CStmt::Comment(text)),
            LoweredOp::None => None,
        }
    }

    fn lower_certified_statement_call(
        &self,
        block_addr: u64,
        op_idx: usize,
        call: CExpr,
        _certified_args: CertifiedCallArgs,
    ) -> LoweredOp {
        if let Some(owner) =
            self.materializable_call_result_expr_for_call_expr((block_addr, op_idx), &call)
        {
            return LoweredOp::Assign {
                lhs: owner,
                rhs: call,
            };
        }
        LoweredOp::Expr(call)
    }

    pub(super) fn lower_op(&self, op: &SSAOp, frame: &mut LowerFrame) -> LoweredOp {
        match frame.mode {
            LowerMode::Expr => LoweredOp::Expr(self.op_to_expr_impl(op)),
            LowerMode::Stmt => {
                if frame.with_call_args {
                    match op {
                        SSAOp::Call { target } => {
                            let direct_target = parse_address_from_var_name(&target.name);
                            let func_expr = self.resolve_call_target_for_site(
                                frame.block_addr,
                                frame.op_idx,
                                target,
                            );
                            let raw_args = self
                                .call_args_map()
                                .get(&(frame.block_addr, frame.op_idx))
                                .cloned()
                                .unwrap_or_default();
                            let Some(mut certified_args) = self
                                .certified_call_args_for_site_with_direct_target(
                                    frame.block_addr,
                                    frame.op_idx,
                                    &func_expr,
                                    direct_target,
                                    raw_args,
                                )
                            else {
                                return LoweredOp::Comment(format!(
                                    "r2sleigh residual: uncertified callsite arguments at 0x{:x}:{}",
                                    frame.block_addr, frame.op_idx
                                ));
                            };
                            let mut args = certified_args.args.clone();
                            if let Some(max_arity) = self
                                .non_variadic_call_arity_for_site_with_direct_target(
                                    frame.block_addr,
                                    frame.op_idx,
                                    direct_target,
                                )
                            {
                                args.truncate(max_arity);
                                certified_args.values.truncate(max_arity);
                            }
                            let call =
                                CExpr::call_at((frame.block_addr, frame.op_idx), func_expr, args);
                            return self.lower_certified_statement_call(
                                frame.block_addr,
                                frame.op_idx,
                                call,
                                certified_args,
                            );
                        }
                        SSAOp::CallInd { target } => {
                            let resolved_target = self.resolve_call_target_for_site(
                                frame.block_addr,
                                frame.op_idx,
                                target,
                            );
                            let func_expr = match resolved_target {
                                CExpr::Var(_) => resolved_target,
                                other => CExpr::Deref(Box::new(other)),
                            };
                            let raw_args = self
                                .call_args_map()
                                .get(&(frame.block_addr, frame.op_idx))
                                .cloned()
                                .unwrap_or_default();
                            let Some(mut certified_args) = self.certified_call_args_for_site(
                                frame.block_addr,
                                frame.op_idx,
                                &func_expr,
                                raw_args,
                            ) else {
                                return LoweredOp::Comment(format!(
                                    "r2sleigh residual: uncertified indirect-call arguments at 0x{:x}:{}",
                                    frame.block_addr, frame.op_idx
                                ));
                            };
                            let mut args = certified_args.args.clone();
                            if let Some(max_arity) = self
                                .non_variadic_call_arity_for_site(frame.block_addr, frame.op_idx)
                            {
                                args.truncate(max_arity);
                                certified_args.values.truncate(max_arity);
                            }
                            let call = CExpr::call(func_expr, args);
                            return self.lower_certified_statement_call(
                                frame.block_addr,
                                frame.op_idx,
                                call,
                                certified_args,
                            );
                        }
                        _ => {}
                    }
                }

                self.op_to_stmt_impl(op)
                    .map(Self::lowered_from_stmt)
                    .unwrap_or(LoweredOp::None)
            }
        }
    }

    pub(crate) fn op_to_expr(&self, op: &SSAOp) -> CExpr {
        let mut frame = LowerFrame::for_expr();
        match self.lower_op(op, &mut frame) {
            LoweredOp::Expr(expr) => expr,
            LoweredOp::Assign { lhs, rhs } => CExpr::assign(lhs, rhs),
            LoweredOp::Return(Some(expr)) => expr,
            LoweredOp::Return(None) => CExpr::External {
                    name: "return".to_string(),
                    kind: crate::symbol::ExternalKind::Intrinsic,
                },
            LoweredOp::Comment(_) | LoweredOp::None => {
                if let Some(dst) = op.dst() {
                    self.name_ref(&self.var_name(dst))
                } else {
                    CExpr::External {
                            name: "__unhandled_op__".to_string(),
                            kind: crate::symbol::ExternalKind::Intrinsic,
                        }
                }
            }
        }
    }

    /// Convert an SSA operation to a C statement, with call argument context.
    pub(super) fn op_to_stmt_with_args(
        &self,
        op: &SSAOp,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<CStmt> {
        let mut frame = LowerFrame::for_stmt(block_addr, op_idx, true);
        let stmt = self.lowered_to_stmt(self.lower_op(op, &mut frame))?;

        if stmt_contains_memory_like_access(&stmt) {
            match op {
                SSAOp::Load { .. } => {
                    if let Some((space, address, value)) = self
                        .certified_memory_access_for_current_op(false)
                        .map(|cert| (cert.space, cert.address, cert.value))
                    {
                        self.record_effect_render_proof_for_memory(
                            EffectRenderProofKind::MemoryRead,
                            block_addr,
                            op_idx,
                            space,
                            Some(address),
                            value,
                        );
                    }
                }
                SSAOp::Store { .. } => {
                    if let Some((space, address, value)) = self
                        .certified_memory_access_for_current_op(true)
                        .map(|cert| (cert.space, cert.address, cert.value))
                    {
                        self.record_effect_render_proof_for_memory(
                            EffectRenderProofKind::MemoryWrite,
                            block_addr,
                            op_idx,
                            space,
                            Some(address),
                            value,
                        );
                    }
                }
                _ => {}
            }
        }
        Some(stmt)
    }
}
