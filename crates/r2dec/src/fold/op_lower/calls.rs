use super::*;

#[derive(Debug, Clone, PartialEq)]
pub(super) struct CertifiedCallArgs {
    pub(super) args: Vec<CExpr>,
    pub(super) values: Vec<r2ssa::ValueId>,
}

fn exact_indexed_call_arguments(
    cert: &r2types::CallsiteArgumentFacts,
    render_fact: &r2types::CallsiteRenderFact,
) -> Option<Vec<(usize, r2ssa::ValueId)>> {
    if cert.callsite != render_fact.callsite
        || render_fact.target != Some(cert.target)
        || cert.argument_values.len() != render_fact.proof_values.len()
    {
        return None;
    }

    let mut indexed = cert
        .argument_values
        .iter()
        .map(|argument| (argument.index, argument.value))
        .collect::<Vec<_>>();
    indexed.sort_unstable_by_key(|(index, _)| *index);
    for (expected_index, (index, value)) in indexed.iter().copied().enumerate() {
        if index != expected_index || render_fact.proof_values.get(index).copied() != Some(value) {
            return None;
        }
    }
    Some(indexed)
}

impl<'a> FoldingContext<'a> {
    pub(super) fn prepared_direct_call_target(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<u64> {
        self.inputs
            .callsite_facts()?
            .arguments_for_site(r2types::CallsiteKey {
                block_addr,
                op_index: op_idx,
            })?
            .direct_target
    }

    /// A reference to the function being called.
    ///
    /// This names something outside the function, so it is an external rather
    /// than a variable. Spelling it as a variable is what let a machine name
    /// look exactly like a local, and it leaves the reader a name no
    /// declaration accounts for.
    pub(super) fn callee_identity_expr(&self, identity: &CalleeIdentity) -> CExpr {
        let name = crate::ast::c_identifier(
            &identity
                .display_name
                .clone()
                .unwrap_or_else(|| identity.primary_key()),
        );
        CExpr::External {
            name,
            kind: external_kind_for_callee(identity.class),
        }
    }

    /// Note the prototype the rendering owes for a call it just lowered.
    ///
    /// C needs a declaration before the call, and this is the point where the
    /// callee's recovered signature is in hand. Where the signature is not
    /// recovered the parameter list is left unspecified rather than asserted,
    /// which is the same distinction `params_known` draws for the function
    /// being rendered: an empty list would claim the callee takes nothing.
    pub(super) fn record_callee_declaration(
        &self,
        func_expr: &CExpr,
        block_addr: u64,
        op_idx: usize,
        args: &CertifiedCallArgs,
    ) {
        let CExpr::External { name, .. } = func_expr.unobserved() else {
            return;
        };
        // The callee's recorded prototype where it has one, and otherwise the
        // widths the call itself proves: the storage its result is defined at
        // and the storage each certified argument occupies. A recorded type
        // that says nothing is worse than the machine's own answer, because it
        // spells `/* unknown */` and the result does not parse.
        let signature = self.known_signature_for_site(block_addr, op_idx);
        let recorded_return = signature
            .as_ref()
            .map(|signature| crate::variable::type_like_to_ctype(&signature.return_type))
            .filter(|ty| !matches!(ty, CType::Unknown));
        let recorded_params = signature.as_ref().and_then(|signature| {
            let params = signature
                .params
                .iter()
                .map(crate::variable::type_like_to_ctype)
                .collect::<Vec<_>>();
            params
                .iter()
                .all(|ty| !matches!(ty, CType::Unknown))
                .then_some(params)
        });
        let declaration = crate::ast::CExternDecl {
            name: name.clone(),
            ret_type: recorded_return.unwrap_or_else(|| {
                self.certified_call_result_value((block_addr, op_idx))
                    .and_then(|value| self.machine_value_width_bits(value))
                    .map_or(CType::Void, CType::UInt)
            }),
            params: recorded_params.or_else(|| {
                args.values
                    .iter()
                    .map(|value| self.machine_value_width_bits(*value).map(CType::UInt))
                    .collect::<Option<Vec<_>>>()
            }),
        };
        self.callee_declarations
            .borrow_mut()
            .entry(declaration.name.clone())
            .or_insert(declaration);
    }

    /// The width a value occupies in machine storage, in bits.
    fn machine_value_width_bits(&self, value: r2ssa::ValueId) -> Option<u32> {
        let graph = self.inputs.prepared_ssa?.graph();
        let size = graph.value(value)?.canonical_storage?.size;
        size.checked_mul(8)
            .filter(|bits| matches!(bits, 8 | 16 | 32 | 64))
    }

    fn resolved_callee_target(
        &self,
        source_call: Option<(u64, usize)>,
        prepared_direct_target: Option<u64>,
    ) -> Option<r2types::ResolvedCalleeTarget> {
        let callsite = source_call.map(|(block_addr, op_idx)| r2types::CallsiteKey {
            block_addr,
            op_index: op_idx,
        });
        let prepared_call_view = source_call
            .and_then(|(block_addr, op_idx)| self.prepared_call_view_for_site(block_addr, op_idx));
        let prepared_identity = prepared_call_view.and_then(|view| view.callee_identity.as_ref());
        let prepared_direct_target = prepared_direct_target
            .or_else(|| prepared_call_view.and_then(|view| view.direct_target))
            .or_else(|| {
                source_call.and_then(|(block_addr, op_idx)| {
                    self.prepared_direct_call_target(block_addr, op_idx)
                })
            });
        r2types::CalleeResolutionFacts::resolve_target_policy(
            r2types::CalleeTargetResolutionRequest {
                identity: r2types::CalleeTargetIdentityRequest {
                    resolution: self.inputs.callee_resolution(),
                    callsite,
                    prepared_identity,
                    prepared_direct_target,
                    direct_target_context: None,
                },
                callee_facts: self.inputs.callee_facts(),
            },
        )
    }

    pub(super) fn resolved_callee_target_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<r2types::ResolvedCalleeTarget> {
        self.resolved_callee_target(Some((block_addr, op_idx)), None)
    }

    pub(super) fn callee_identity_for_callsite(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<CalleeIdentity> {
        self.resolved_callee_target_for_site(block_addr, op_idx)
            .map(|target| target.identity)
    }

    pub(super) fn resolved_callee_identity_expr_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<CExpr> {
        self.resolved_callee_target_for_site(block_addr, op_idx)
            .map(|target| self.callee_identity_expr(&target.identity))
    }

    pub(super) fn resolve_call_target_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
        target: &SSAVar,
    ) -> OpLoweringResult<CExpr> {
        if let Some(resolved) = self.resolved_callee_identity_expr_for_site(block_addr, op_idx) {
            return Ok(resolved);
        }
        self.resolve_call_target(target)
    }

    pub(super) fn admitted_callsite(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> OpLoweringResult<(
        &r2types::CallsiteArgumentFacts,
        &r2types::CallsiteRenderFact,
    )> {
        let cert = self
            .certified_callsite_for_op(block_addr, op_idx)
            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
        let render_fact = self
            .certified_call_render_fact_for_op(block_addr, op_idx)
            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
        let expected_site = r2types::CallsiteKey {
            block_addr,
            op_index: op_idx,
        };
        if cert.callsite != expected_site
            || render_fact.callsite != expected_site
            || render_fact.target != Some(cert.target)
            || matches!(
                render_fact.disposition,
                r2types::CallsiteRenderDisposition::Suppressed
                    | r2types::CallsiteRenderDisposition::Residualized
            )
        {
            return Err(OpLoweringRefusal::missing_machine_projection());
        }
        Ok((cert, render_fact))
    }

    pub(super) fn certified_call_args_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> OpLoweringResult<CertifiedCallArgs> {
        let (cert, render_fact) = self.admitted_callsite(block_addr, op_idx)?;
        let indexed = exact_indexed_call_arguments(cert, render_fact)
            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
        let proof = self
            .certified_render_context()
            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;

        let render_plan = self.certified_render_plan(proof);
        let args = indexed
            .iter()
            .copied()
            .map(|(index, value)| {
                self.certified_call_arg_expr_for_value_at_site(
                    (block_addr, op_idx),
                    index,
                    value,
                    render_plan.as_ref(),
                )
            })
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
        Ok(CertifiedCallArgs {
            args,
            values: indexed.into_iter().map(|(_, value)| value).collect(),
        })
    }

    /// One argument of a call, spelled by the plan and observed as a read.
    ///
    /// The render plan says which value belongs at this index. The binding
    /// plan says how that value is read, exactly as it does for an operand of
    /// any other operation, so the argument is whatever the value's own
    /// disposition renders as.
    ///
    /// The read itself has no `UseSite`: `SSAOp::Call` takes only the callee
    /// as an operand, so an argument value is consumed by the call boundary
    /// and not by the graph. The callsite certificate is the source's record
    /// that the read happens, which is the same record the return boundary
    /// keeps for the value a `Return` carries, and it authorizes the marker
    /// the same way.
    fn certified_call_arg_expr_for_value_at_site(
        &self,
        site: (u64, usize),
        index: usize,
        value: r2ssa::ValueId,
        render_plan: Option<&CertifiedRenderPlan<'_>>,
    ) -> Option<CExpr> {
        if !render_plan?.admits_call_arg(site, index, value) {
            return None;
        }
        let expr = match self.planned_value_expr(value) {
            Ok(expr) => expr,
            Err(error) => {
                self.retain_first_observation_error(error);
                return None;
            }
        };
        // An inlined constant is spelled as a literal and reads no program
        // variable, so there is no read for the placement audit to authorize
        // and nothing for a marker to name.
        if !matches!(
            self.inputs
                .binding_names
                .and_then(|names| names.disposition_for_value(value)),
            Some(crate::binding_plan::ValueDisposition::Bound { .. })
        ) {
            return Some(expr);
        }
        let at = self
            .inputs
            .prepared_ssa?
            .graph()
            .inst_id_for_op_site(site.0, site.1)?;
        Some(self.observe_certified_value_read_expr(value, at, expr))
    }

    pub(super) fn known_signature_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<r2types::FunctionType> {
        self.callee_identity_for_callsite(block_addr, op_idx)
            .and_then(|identity| identity.known_signature().cloned())
    }

    pub(super) fn resolve_call_target(&self, target: &SSAVar) -> OpLoweringResult<CExpr> {
        if let Some(addr) = self.certified_const_bits(target) {
            return Ok(self.callee_identity_expr(&self.callee_identity_for_direct_target(addr)));
        }
        if target.name_kind().is_constant() {
            return Err(OpLoweringRefusal::missing_program_variable());
        }
        let value = self
            .prepared_value_id_for_var(target)
            .ok_or_else(|| OpLoweringRefusal::missing_program_variable())?;
        match self.planned_value_expr(value) {
            Ok(expr) => Ok(expr),
            Err(error) => {
                self.retain_first_observation_error(error);
                Err(OpLoweringRefusal::missing_program_variable())
            }
        }
    }

    #[cfg(test)]
    pub(super) fn is_modeled_call_target_for_site(&self, block_addr: u64, op_idx: usize) -> bool {
        self.resolved_callee_target_for_site(block_addr, op_idx)
            .is_some_and(|target| target.policy.modeled)
    }
}

/// What kind of outside thing a call names.
///
/// The identity already classified it, so the rendering says what the analysis
/// concluded rather than guessing from how the name is spelled.
fn external_kind_for_callee(class: r2types::CalleeClass) -> crate::symbol::ExternalKind {
    match class {
        r2types::CalleeClass::Imported => crate::symbol::ExternalKind::Import,
        r2types::CalleeClass::ExternalSymbol => crate::symbol::ExternalKind::Global,
        _ => crate::symbol::ExternalKind::Function,
    }
}

#[cfg(test)]
mod indexed_argument_tests {
    use super::exact_indexed_call_arguments;

    fn facts(
        arguments: &[(usize, u32)],
        proof_values: &[u32],
    ) -> (r2types::CallsiteArgumentFacts, r2types::CallsiteRenderFact) {
        let callsite = r2types::CallsiteKey {
            block_addr: 0x1000,
            op_index: 2,
        };
        (
            r2types::CallsiteArgumentFacts {
                callsite,
                call_site_id: r2ssa::CallSiteId(0),
                at: r2ssa::InstId(0),
                target: r2ssa::ValueId(9),
                direct_target: Some(0x401000),
                argument_values: arguments
                    .iter()
                    .map(|(index, value)| r2types::CallArgumentValueFact {
                        index: *index,
                        value: r2ssa::ValueId(*value),
                    })
                    .collect(),
                register_argument_locations: Vec::new(),
                stack_argument_locations: Vec::new(),
            },
            r2types::CallsiteRenderFact {
                callsite,
                target: Some(r2ssa::ValueId(9)),
                disposition: r2types::CallsiteRenderDisposition::SideEffectStatement,
                proof_values: proof_values.iter().copied().map(r2ssa::ValueId).collect(),
                residual_reason: None,
            },
        )
    }

    #[test]
    fn indexed_arguments_require_one_contiguous_value_per_index() {
        let (cert, render) = facts(&[(1, 11), (0, 10)], &[10, 11]);
        assert_eq!(
            exact_indexed_call_arguments(&cert, &render),
            Some(vec![(0, r2ssa::ValueId(10)), (1, r2ssa::ValueId(11))])
        );

        for arguments in [&[(0, 10), (0, 11)][..], &[(0, 10), (2, 11)][..]] {
            let (cert, render) = facts(arguments, &[10, 11]);
            assert_eq!(exact_indexed_call_arguments(&cert, &render), None);
        }
    }

    #[test]
    fn indexed_arguments_require_matching_render_proof_slot() {
        let (cert, render) = facts(&[(0, 10), (1, 11)], &[10, 12]);
        assert_eq!(exact_indexed_call_arguments(&cert, &render), None);
    }
}
