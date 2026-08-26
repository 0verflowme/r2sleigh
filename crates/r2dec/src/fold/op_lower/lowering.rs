use super::calls::CertifiedCallArgs;
use super::projection::{project_machine_use, project_machine_write};
use super::*;

impl<'a> FoldingContext<'a> {
    fn observation_lowering_refusal(
        error: &crate::observation_journal::LegacyObservationJournalError,
    ) -> OpLoweringRefusal {
        use crate::observation_journal::LegacyObservationJournalError as Error;
        match error {
            Error::RenderedValueRequired(_)
            | Error::InvalidPlannedInline { .. }
            | Error::PlannedElidedValueRendered { .. }
            | Error::PlannedRefusedValueRendered { .. }
            | Error::MissingPlannedValue(_) => {
                OpLoweringRefusal::MissingProgramVariableAuthorization
            }
            _ => OpLoweringRefusal::MissingMachineProjectionAuthorization,
        }
    }

    fn exact_normalized_op_effects(
        &self,
        op: &SSAOp,
        block_addr: u64,
        op_idx: usize,
        contains_memory: bool,
    ) -> std::collections::BTreeSet<r2ssa::SemanticObligationId> {
        let mut obligations = self.exact_effect_obligations_for_normalized_value(
            EffectOccurrenceKind::Expression,
            block_addr,
            op_idx,
            op.dst().and_then(|dst| self.value_id_for_rendered_op(dst)),
        );
        if contains_memory {
            let memory = match op {
                SSAOp::Load { .. } => self
                    .certified_memory_access_for_current_op(false)
                    .map(|cert| (EffectOccurrenceKind::MemoryRead, cert)),
                SSAOp::Store { .. } => self
                    .certified_memory_access_for_current_op(true)
                    .map(|cert| (EffectOccurrenceKind::MemoryWrite, cert)),
                _ => None,
            };
            if let Some((kind, cert)) = memory {
                obligations.extend(self.exact_effect_obligations_for_normalized_memory(
                    kind,
                    block_addr,
                    op_idx,
                    cert.space,
                    Some(cert.address),
                    cert.value,
                ));
            }
        }
        obligations
    }

    fn normalized_output_projection(
        &self,
        site: crate::normalize::NormalizedOpSite,
    ) -> Result<crate::normalize::NormalizedOutputProjection, crate::observation_journal::LegacyObservationJournalError,
    >
    {
        let prepared = self.inputs.prepared_ssa.ok_or(
            crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
        )?;
        self.inputs
            .normalization_origins
            .ok_or(
                crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
            )?
            .projection(site, prepared)
            .map_err(crate::observation_journal::LegacyObservationJournalError::Normalization)?
            .ok_or(
                crate::observation_journal::LegacyObservationJournalError::InvalidNormalizedSite(
                    site,
                ),
            )?
            .output
            .ok_or(
                crate::observation_journal::LegacyObservationJournalError::MissingNormalizedOutput(
                    site,
                ),
            )
    }

    fn project_planned_assignment(
        &self,
        site: Option<crate::normalize::NormalizedOpSite>,
        lhs: CExpr,
        rhs: CExpr,
    ) -> Result<(CExpr, CExpr), crate::observation_journal::LegacyObservationJournalError> {
        let Some(site) = site else {
            return Ok((lhs, rhs));
        };
        let output = self.normalized_output_projection(site)?;
        let Some(names) = self.inputs.binding_names else {
            return Err(
                crate::observation_journal::LegacyObservationJournalError::MissingPlannedValue(
                    output.value,
                ),
            );
        };
        match names.require_write(output.inst) {
            Ok(r2ssa::MachineWriteDisposition::Exact(projection)) => {
                project_machine_write(lhs, rhs, *projection).map_err(|_| {
                    crate::observation_journal::LegacyObservationJournalError::RefusedRenderedWrite(
                        output.inst,
                    )
                })
            }
            Ok(r2ssa::MachineWriteDisposition::Refused(_)) => {
                unreachable!("require_write cannot return a refused disposition")
            }
            Err(crate::binding_plan::RenderedIdentityRefusal::MachineWrite { .. }) => Err(
                crate::observation_journal::LegacyObservationJournalError::RefusedRenderedWrite(
                    output.inst,
                ),
            ),
            Err(_) => Err(
                crate::observation_journal::LegacyObservationJournalError::InvalidWrite(output.inst),
            ),
        }
    }

    fn project_lowered_assignment(
        &self,
        site: Option<crate::normalize::NormalizedOpSite>,
        lowered: LoweredOp,
    ) -> OpLoweringResult<LoweredOp> {
        let LoweredOp::Assign { lhs, rhs } = lowered else {
            return Ok(lowered);
        };
        match self.project_planned_assignment(site, lhs.clone(), rhs.clone()) {
            Ok((lhs, rhs)) => Ok(LoweredOp::Assign { lhs, rhs }),
            Err(error) => {
                let refusal = Self::observation_lowering_refusal(&error);
                self.retain_first_observation_error(error);
                Err(refusal)
            }
        }
    }

    /// Apply a source write only when the finalized statement targets the
    /// exact plan-owned output binding. A different target has no typed
    /// synthetic-origin certificate, so it cannot waive the `InstId` write
    /// projection.
    fn project_finalized_assignment_stmt(
        &self,
        site: Option<crate::normalize::NormalizedOpSite>,
        stmt: CStmt,
    ) -> OpLoweringResult<CStmt> {
        let Some(site) = site else {
            return Ok(stmt);
        };
        let output = match self.normalized_output_projection(site) {
            Ok(output) => output,
            Err(error) => {
                self.retain_first_observation_error(error);
                return Err(OpLoweringRefusal::MissingMachineProjectionAuthorization);
            }
        };
        let Some(names) = self.inputs.binding_names else {
            return Err(OpLoweringRefusal::MissingProgramVariableAuthorization);
        };
        let symbol = match names.require_value(output.value) {
            Ok(crate::binding_plan::PlannedValueSymbol::Bound(symbol)) => symbol,
            Ok(
                crate::binding_plan::PlannedValueSymbol::Inline(_)
                | crate::binding_plan::PlannedValueSymbol::Elided(_),
            ) => return Ok(stmt),
            Ok(
                crate::binding_plan::PlannedValueSymbol::Refused(_)
                | crate::binding_plan::PlannedValueSymbol::Absent,
            ) => unreachable!("require_value cannot return an absent or refused disposition"),
            Err(_) => return Err(OpLoweringRefusal::MissingProgramVariableAuthorization),
        };
        let CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) = stmt
        else {
            return Ok(stmt);
        };
        let lhs = *left;
        let rhs = *right;
        let planned_lhs = CExpr::Var(symbol);
        if !lhs.transparently_eq(&planned_lhs) {
            return Err(OpLoweringRefusal::MissingProgramVariableAuthorization);
        }
        match self.project_planned_assignment(Some(site), lhs.clone(), rhs.clone()) {
            Ok((lhs, rhs)) => Ok(CStmt::Expr(CExpr::assign(lhs, rhs))),
            Err(error) => {
                let refusal = Self::observation_lowering_refusal(&error);
                self.retain_first_observation_error(error);
                Err(refusal)
            }
        }
    }

    pub(crate) fn planned_value_expr(
        &self,
        value: ValueId,
    ) -> Result<CExpr, crate::observation_journal::LegacyObservationJournalError> {
        let Some(names) = self.inputs.binding_names else {
            return Err(
                crate::observation_journal::LegacyObservationJournalError::RenderedValueRequired(
                    value,
                ),
            );
        };
        match names.require_value(value) {
            Ok(crate::binding_plan::PlannedValueSymbol::Bound(symbol)) => Ok(CExpr::Var(symbol)),
            Ok(crate::binding_plan::PlannedValueSymbol::Inline(expr)) => {
                let Some(machine_expr) = names.inline_expr(expr) else {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidPlannedInline {
                            value,
                            expr,
                        },
                    );
                };
                let r2ssa::MachineExprKind::Constant {
                    binding,
                    value: literal,
                } = machine_expr.kind()
                else {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidPlannedInline {
                            value,
                            expr,
                        },
                    );
                };
                if binding.value() != value {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidPlannedInline {
                            value,
                            expr,
                        },
                    );
                }
                let bits = literal.bits();
                Ok(if bits > i64::MAX as u64 {
                    CExpr::UIntLit(bits)
                } else {
                    CExpr::IntLit(bits as i64)
                })
            }
            Ok(crate::binding_plan::PlannedValueSymbol::Elided(reason)) => Err(
                crate::observation_journal::LegacyObservationJournalError::PlannedElidedValueRendered {
                    value,
                    reason,
                },
            ),
            Ok(
                crate::binding_plan::PlannedValueSymbol::Refused(_)
                | crate::binding_plan::PlannedValueSymbol::Absent,
            ) => unreachable!("require_value cannot return an absent or refused disposition"),
            Err(crate::binding_plan::RenderedIdentityRefusal::Value { reason, .. }) => Err(
                crate::observation_journal::LegacyObservationJournalError::PlannedRefusedValueRendered {
                    value,
                    reason,
                },
            ),
            Err(_) => Err(
                crate::observation_journal::LegacyObservationJournalError::MissingPlannedValue(
                    value,
                ),
            ),
        }
    }

    fn planned_input_expr(
        &self,
        frame: &LowerFrame,
        input_idx: usize,
        contextual_expr: CExpr,
    ) -> Result<CExpr, crate::observation_journal::LegacyObservationJournalError> {
        let site = frame.normalized_site.ok_or(
            crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
        )?;
        let prepared = self.inputs.prepared_ssa.ok_or(
            crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
        )?;
        let projection = self
            .inputs
            .normalization_origins
            .ok_or(
                crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
            )?
            .projection(site, prepared)
            .map_err(crate::observation_journal::LegacyObservationJournalError::Normalization)?
            .ok_or(
                crate::observation_journal::LegacyObservationJournalError::InvalidNormalizedSite(
                    site,
                ),
            )?;
        let input = projection.inputs.get(input_idx).ok_or(
            crate::observation_journal::LegacyObservationJournalError::InvalidNormalizedInput {
                site,
                input_idx,
            },
        )?;
        let Some(first_site) = input.uses.first().copied() else {
            // Synthetic preservation inputs have no original graph use and
            // therefore no source-owned projection to apply.
            return Ok(self.observe_optional_normalized_input_value_expr(
                frame.normalized_site,
                input_idx,
                self.planned_value_expr(input.value)?,
            ));
        };
        let Some(names) = self.inputs.binding_names else {
            return Err(
                crate::observation_journal::LegacyObservationJournalError::RenderedValueRequired(
                    input.value,
                ),
            );
        };
        let first_disposition = match names.require_use(first_site) {
            Ok(disposition @ (r2ssa::MachineUseDisposition::Exact(_)
            | r2ssa::MachineUseDisposition::MemoryAddress(_)),
            ) => *disposition,
            Ok(r2ssa::MachineUseDisposition::Refused(_)) => {
                unreachable!("require_use cannot return a refused disposition")
            }
            Err(crate::binding_plan::RenderedIdentityRefusal::MachineUse { .. }) => {
                return Err(
                    crate::observation_journal::LegacyObservationJournalError::RefusedRenderedUse(
                        first_site,
                    ),
                );
            }
            Err(_) => {
                return Err(
                    crate::observation_journal::LegacyObservationJournalError::InvalidUse(
                        first_site,
                    ),
                );
            }
        };
        for use_site in input.uses.iter().copied().skip(1) {
            match names.require_use(use_site) {
                Ok(disposition) if *disposition == first_disposition => {}
                Ok(r2ssa::MachineUseDisposition::Refused(_)) => {
                    unreachable!("require_use cannot return a refused disposition")
                }
                Err(crate::binding_plan::RenderedIdentityRefusal::MachineUse { .. }) => {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::RefusedRenderedUse(
                            use_site,
                        ),
                    );
                }
                Ok(
                    r2ssa::MachineUseDisposition::Exact(_)
                    | r2ssa::MachineUseDisposition::MemoryAddress(_),
                ) => {
                    // One relocated normalized expression cannot implement two
                    // different source projections. Keep the normalized site
                    // typed and refuse the projection instead of choosing one.
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidNormalizedInput {
                            site,
                            input_idx,
                        },
                    );
                }
                Err(_) => {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidUse(
                            use_site,
                        ),
                    );
                }
            }
        }
        match first_disposition {
            r2ssa::MachineUseDisposition::Exact(slice) => {
                let base = self.observe_optional_normalized_input_value_expr(
                    frame.normalized_site,
                    input_idx,
                    self.planned_value_expr(input.value)?,
                );
                project_machine_use(base, slice).map_err(|_| {
                    // The machine use is exact, but the strict C dialect cannot spell
                    // this projection without more type evidence. Refuse the emitted
                    // occurrence instead of inventing an integer or pointer type.
                    crate::observation_journal::LegacyObservationJournalError::RefusedRenderedUse(
                        first_site,
                    )
                })
            }
            r2ssa::MachineUseDisposition::MemoryAddress(address) => {
                if address.binding().value() != input.value
                    || address.memory_access().is_none()
                {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidUse(
                            first_site,
                        ),
                    );
                }
                // The load/store renderer has already consumed the source-owned
                // structured-access certificate. Preserve that contextual AST:
                // substituting the value's ordinary binding here would turn a
                // certified stack/object access back into an SP/RBP expression.
                // This node is the contextual projection, not an occurrence
                // of the value's ordinary binding. Mark only the exact
                // `UseSite`; wrapping it as a bound `ValueId` would make the
                // audit claim that a C variable was rendered where the AST in
                // fact contains a structured memory access.
                Ok(contextual_expr)
            }
            r2ssa::MachineUseDisposition::Refused(_) => {
                unreachable!(
                "the refused source use returned before projection"
            )
            }
        }
    }

    pub(super) fn planned_current_output_expr(
        &self,
    ) -> Result<Option<CExpr>, crate::observation_journal::LegacyObservationJournalError> {
        if self.inputs.observation_journal.is_none() {
            return Ok(None);
        }
        let Some(block_addr) = self.current_block_addr.get() else {
            return Ok(None);
        };
        let Some(op_idx) = self.current_op_idx.get() else {
            return Ok(None);
        };
        let site = self.normalized_site(block_addr, op_idx).ok_or(
            crate::observation_journal::LegacyObservationJournalError::MissingNormalizedBlock(
                block_addr,
            ),
        )?;
        let value = self.normalized_output_projection(site)?.value;
        let Some(names) = self.inputs.binding_names else {
            return Err(crate::observation_journal::LegacyObservationJournalError::MissingPlannedValue(value));
        };
        match names.require_value(value) {
            Ok(crate::binding_plan::PlannedValueSymbol::Bound(symbol)) => {
                Ok(Some(CExpr::Var(symbol)))
            }
            Ok(crate::binding_plan::PlannedValueSymbol::Inline(expr)) => Err(
                crate::observation_journal::LegacyObservationJournalError::InvalidPlannedInline {
                    value,
                    expr,
                },
            ),
            // An attempted lowering is not a rendered occurrence. Keep the
            // legacy candidate long enough for dead-code and structuring
            // rewrites to delete it; the final surviving value marker is the
            // only place allowed to turn either disposition into an error.
            Ok(
                crate::binding_plan::PlannedValueSymbol::Elided(_)
            ) => Ok(None),
            Ok(
                crate::binding_plan::PlannedValueSymbol::Refused(_)
                | crate::binding_plan::PlannedValueSymbol::Absent,
            ) => unreachable!("require_value cannot return an absent or refused disposition"),
            Err(crate::binding_plan::RenderedIdentityRefusal::Value { reason, .. }) => Err(
                crate::observation_journal::LegacyObservationJournalError::PlannedRefusedValueRendered {
                    value,
                    reason,
                },
            ),
            Err(_) => Err(
                crate::observation_journal::LegacyObservationJournalError::MissingPlannedValue(
                    value,
                ),
            ),
        }
    }

    pub(super) fn observed_input(
        &self,
        frame: &LowerFrame,
        input_idx: usize,
        expr: CExpr,
    ) -> CExpr {
        if frame.observe_inputs {
            let expr = match self.planned_input_expr(frame, input_idx, expr.clone()) {
                Ok(planned) => planned,
                Err(error) => {
                    let refusal = Self::observation_lowering_refusal(&error);
                    self.retain_first_observation_error(error);
                    self.retain_first_lowering_refusal(refusal);
                    return expr;
                }
            };
            self.observe_optional_normalized_input_uses_expr(
                frame.normalized_site,
                input_idx,
                expr,
            )
        } else {
            expr
        }
    }

    pub(super) fn lowered_from_stmt(stmt: CStmt) -> LoweredOp {
        match stmt {
            CStmt::Empty => LoweredOp::None,
            stmt => LoweredOp::FinalizedStmt(stmt),
        }
    }

    pub(super) fn lowered_to_stmt(&self, lowered: LoweredOp) -> Option<CStmt> {
        match lowered {
            LoweredOp::Assign { lhs, rhs } => self.assign_stmt(lhs, rhs),
            LoweredOp::FinalizedStmt(stmt) => Some(stmt),
            LoweredOp::Expr(expr) => Some(CStmt::Expr(expr)),
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

    pub(super) fn lower_op(
        &self,
        op: &SSAOp,
        frame: &mut LowerFrame,
    ) -> OpLoweringResult<LoweredOp> {
        self.pending_lowering_refusal.set(None);
        let lowered = match frame.mode {
            LowerMode::Expr => self
                .op_to_expr_impl(op, frame)?
                .map(LoweredOp::Expr)
                .unwrap_or(LoweredOp::None),
            LowerMode::Stmt => {
                if frame.with_call_args {
                    match op {
                        SSAOp::Call { target } => {
                            let Some((source_block, source_op_idx)) = frame.source_call_site else {
                                return Ok(LoweredOp::Comment(
                                    "r2sleigh residual: missing exact source callsite".to_string(),
                                ));
                            };
                            let direct_target = parse_address_from_var_name(&target.name);
                            let func_expr = self.resolve_call_target_for_site(
                                source_block,
                                source_op_idx,
                                target,
                            );
                            let func_expr = self.observed_input(frame, 0, func_expr);
                            let raw_args = self
                                .call_args_map()
                                .get(&(source_block, source_op_idx))
                                .cloned()
                                .unwrap_or_default();
                            let Some(mut certified_args) = self
                                .certified_call_args_for_site_with_direct_target(
                                    source_block,
                                    source_op_idx,
                                    &func_expr,
                                    direct_target,
                                    raw_args,
                                )
                            else {
                                return self.finish_lowering_transaction(LoweredOp::Comment(format!(
                                    "r2sleigh residual: uncertified callsite arguments at 0x{:x}:{}",
                                    source_block, source_op_idx
                                )));
                            };
                            let mut args = certified_args.args.clone();
                            if let Some(max_arity) = self
                                .non_variadic_call_arity_for_site_with_direct_target(
                                    source_block,
                                    source_op_idx,
                                    direct_target,
                                )
                            {
                                args.truncate(max_arity);
                                certified_args.values.truncate(max_arity);
                            }
                            let call =
                                CExpr::call_at((source_block, source_op_idx), func_expr, args);
                            return self.finish_lowering_transaction(self.lower_certified_statement_call(
                                source_block,
                                source_op_idx,
                                call,
                                certified_args,
                            ));
                        }
                        SSAOp::CallInd { target } => {
                            let Some((source_block, source_op_idx)) = frame.source_call_site else {
                                return Ok(LoweredOp::Comment(
                                    "r2sleigh residual: missing exact source callsite".to_string(),
                                ));
                            };
                            let resolved_target = self.resolve_call_target_for_site(
                                source_block,
                                source_op_idx,
                                target,
                            );
                            let resolved_target = self.observed_input(frame, 0, resolved_target);
                            let func_expr = Self::indirect_callable_expr(resolved_target);
                            let raw_args = self
                                .call_args_map()
                                .get(&(source_block, source_op_idx))
                                .cloned()
                                .unwrap_or_default();
                            let Some(mut certified_args) = self.certified_call_args_for_site(
                                source_block,
                                source_op_idx,
                                &func_expr,
                                raw_args,
                            ) else {
                                return self.finish_lowering_transaction(LoweredOp::Comment(format!(
                                    "r2sleigh residual: uncertified indirect-call arguments at 0x{:x}:{}",
                                    source_block, source_op_idx
                                )));
                            };
                            let mut args = certified_args.args.clone();
                            if let Some(max_arity) =
                                self.non_variadic_call_arity_for_site(source_block, source_op_idx)
                            {
                                args.truncate(max_arity);
                                certified_args.values.truncate(max_arity);
                            }
                            let call = CExpr::call_at(
                                (source_block, source_op_idx),
                                func_expr,
                                args,
                            );
                            return self.finish_lowering_transaction(self.lower_certified_statement_call(
                                source_block,
                                source_op_idx,
                                call,
                                certified_args,
                            ));
                        }
                        _ => {}
                    }
                }

                self.op_to_stmt_impl(op, frame)?
                    .map(Self::lowered_from_stmt)
                    .unwrap_or(LoweredOp::None)
            }
        };
        self.finish_lowering_transaction(lowered)
    }

    fn finish_lowering_transaction(&self, lowered: LoweredOp) -> OpLoweringResult<LoweredOp> {
        match self.pending_lowering_refusal.take() {
            Some(refusal) => Err(refusal),
            None => Ok(lowered),
        }
    }

    pub(crate) fn op_to_expr(&self, op: &SSAOp) -> OpLoweringResult<CExpr> {
        let mut frame = LowerFrame::for_expr();
        Ok(match self.lower_op(op, &mut frame)? {
            LoweredOp::Expr(expr) => expr,
            LoweredOp::Assign { lhs, rhs } => CExpr::assign(lhs, rhs),
            LoweredOp::FinalizedStmt(CStmt::Expr(expr)) => expr,
            LoweredOp::FinalizedStmt(CStmt::Return(Some(expr))) => expr,
            LoweredOp::FinalizedStmt(_) => {
                return Err(OpLoweringRefusal::UnrepresentableOperation);
            }
            LoweredOp::Comment(_) | LoweredOp::None => {
                return Err(OpLoweringRefusal::UnrepresentableOperation);
            }
        })
    }

    pub(crate) fn op_to_expr_at(
        &self,
        op: &SSAOp,
        block_addr: u64,
        op_idx: usize,
    ) -> OpLoweringResult<LoweredExprAt> {
        // Operand observations are attached while their exact expression
        // positions still exist. Wrapping the completed expression once per
        // input would falsely make every operand own the same aggregate node.
        let normalized_site = self.normalized_site(block_addr, op_idx);
        let mut frame = LowerFrame::for_observed_expr(normalized_site);
        let lowered = self.project_lowered_assignment(
            normalized_site,
            self.lower_op(op, &mut frame)?,
        )?;
        let lowered = match lowered {
            LoweredOp::Expr(expr) => LoweredExprAt::Rendered(expr),
            LoweredOp::Assign { lhs, rhs } => LoweredExprAt::Rendered(CExpr::assign(lhs, rhs)),
            LoweredOp::FinalizedStmt(CStmt::Expr(expr)) => LoweredExprAt::Rendered(expr),
            LoweredOp::FinalizedStmt(CStmt::Return(Some(expr))) => LoweredExprAt::Rendered(expr),
            LoweredOp::FinalizedStmt(_) => {
                return Err(OpLoweringRefusal::UnrepresentableOperation);
            }
            LoweredOp::Comment(_) | LoweredOp::None => {
                return Err(OpLoweringRefusal::UnrepresentableOperation);
            }
        };
        Ok(match lowered {
            LoweredExprAt::Rendered(expr) => {
                let obligations = self.exact_normalized_op_effects(
                    op,
                    block_addr,
                    op_idx,
                    expr_contains_memory_like_access(&expr),
                );
                let expr = if op.dst().is_some() {
                    self.observe_normalized_output_expr(block_addr, op_idx, expr)
                } else {
                    expr
                };
                LoweredExprAt::Rendered(self.observe_effect_expr(&obligations, expr))
            }
        })
    }

    /// Attach only the exact result identity to a custom producer expression.
    ///
    /// Its operand positions no longer correspond to ordinary opcode lowering,
    /// so claiming them on the aggregate expression would relocate every input.
    pub(crate) fn observe_normalized_result_expr(
        &self,
        op: &SSAOp,
        block_addr: u64,
        op_idx: usize,
        expr: CExpr,
    ) -> CExpr {
        if op.dst().is_some() {
            self.observe_normalized_output_expr(block_addr, op_idx, expr)
        } else {
            expr
        }
    }

    /// Convert an SSA operation to a C statement, with call argument context.
    pub(super) fn op_to_stmt_with_args(
        &self,
        op: &SSAOp,
        block_addr: u64,
        op_idx: usize,
    ) -> OpLoweringResult<Option<CStmt>> {
        let source_site = self.source_op_site_for_normalized_op(block_addr, op_idx);
        if matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) && source_site.is_none() {
            return Ok(Some(self.certified_residual_comment(format!(
                "synthetic operation cannot carry callsite facts at 0x{block_addr:x}:{op_idx}"
            ))));
        }
        let normalized_site = self.normalized_site(block_addr, op_idx);
        let source_call_site = source_site.or(Some((block_addr, op_idx)));
        let mut frame = LowerFrame::for_stmt(normalized_site, source_call_site, true);
        let lowered = self.lower_op(op, &mut frame)?;
        let Some(stmt) = self.lowered_to_stmt(lowered) else {
            return Ok(None);
        };
        let stmt = self.project_finalized_assignment_stmt(normalized_site, stmt)?;

        let obligations = self.exact_normalized_op_effects(
            op,
            block_addr,
            op_idx,
            stmt_contains_memory_like_access(&stmt),
                        );
        let stmt = if op.dst().is_some()
            && !matches!(stmt.unobserved(), CStmt::Comment(_) | CStmt::Empty)
        {
            self.observe_normalized_output_stmt(block_addr, op_idx, stmt)
        } else {
            stmt
        };
        Ok(Some(self.observe_effect_stmt(&obligations, stmt)))
    }

    /// Render one resolved indirect-call target without letting occurrence
    /// metadata change whether an already-callable variable is dereferenced.
    pub(super) fn indirect_callable_expr(resolved_target: CExpr) -> CExpr {
        match resolved_target.unobserved() {
            CExpr::Var(_) => resolved_target,
            _ => CExpr::Deref(Box::new(resolved_target)),
        }
    }
}
