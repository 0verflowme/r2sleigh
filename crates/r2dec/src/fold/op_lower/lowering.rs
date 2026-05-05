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

    pub(super) fn lower_op(&self, op: &SSAOp, frame: &mut LowerFrame) -> LoweredOp {
        match frame.mode {
            LowerMode::Expr => LoweredOp::Expr(self.op_to_expr_impl(op)),
            LowerMode::Stmt => {
                if frame.with_call_args {
                    match op {
                        SSAOp::Call { target } => {
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
                            let mut args = self
                                .prepared_call_args_for_site(
                                    frame.block_addr,
                                    frame.op_idx,
                                    &func_expr,
                                )
                                .unwrap_or_else(|| {
                                    self.render_call_args_for_callee(&func_expr, raw_args)
                                });
                            if let Some(max_arity) = self.non_variadic_call_arity(&func_expr) {
                                args.truncate(max_arity);
                            }
                            let call = CExpr::call(func_expr, args);
                            if let Some(owner) = self.materializable_call_result_expr_for_call_expr(
                                (frame.block_addr, frame.op_idx),
                                &call,
                            ) {
                                return LoweredOp::Assign {
                                    lhs: owner,
                                    rhs: call,
                                };
                            }
                            return LoweredOp::Expr(call);
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
                            let mut args = self
                                .prepared_call_args_for_site(
                                    frame.block_addr,
                                    frame.op_idx,
                                    &func_expr,
                                )
                                .unwrap_or_else(|| {
                                    self.render_call_args_for_callee(&func_expr, raw_args)
                                });
                            if let Some(max_arity) = self.non_variadic_call_arity(&func_expr) {
                                args.truncate(max_arity);
                            }
                            let call = CExpr::call(func_expr, args);
                            if let Some(owner) = self.materializable_call_result_expr_for_call_expr(
                                (frame.block_addr, frame.op_idx),
                                &call,
                            ) {
                                return LoweredOp::Assign {
                                    lhs: owner,
                                    rhs: call,
                                };
                            }
                            return LoweredOp::Expr(call);
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
            LoweredOp::Return(None) => CExpr::Var("return".to_string()),
            LoweredOp::Comment(_) | LoweredOp::None => {
                if let Some(dst) = op.dst() {
                    CExpr::Var(self.var_name(dst))
                } else {
                    CExpr::Var("__unhandled_op__".to_string())
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
        self.lowered_to_stmt(self.lower_op(op, &mut frame))
    }
}
