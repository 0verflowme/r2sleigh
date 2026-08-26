use std::cell::RefCell;
use std::rc::Rc;

use r2ssa::{
    InstId, MachineExprId, MachineUseDisposition, MachineUseRefusal, MachineWriteDisposition,
    MachineWriteRefusal, ObjectId, SsaArtifactAuthority, UseSite, ValueId,
};
use r2types::SourceOwnedFunctionFacts;

use super::{
    BindingId, BindingPlan, BindingPlanSourceMismatch, BindingRole, ParameterDisposition,
    ParameterRefusal, StackObjectDisposition, StackObjectRefusal, ValueDisposition, ValueRefusal,
};
use crate::symbol::{SymbolId, SymbolRole, SymbolTable};

/// Exact naming answer for one SSA value in a sealed binding plan.
///
/// Expression identities and typed reasons are copied out of the plan only as
/// stable evidence keys. The inline and dead-value proofs remain owned by the
/// plan and are not reconstructed here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlannedValueSymbol {
    Bound(SymbolId),
    Inline(MachineExprId),
    Elided(r2ssa::ledger::ElisionReason),
    Refused(ValueRefusal),
    Absent,
}

/// Exact naming answer for one source-owned stack object.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlannedStackSymbol {
    Bound(SymbolId),
}

/// Exact identifier answer for one certified ABI parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlannedParameterSymbol {
    Bound { symbol: SymbolId, width_bits: u32 },
}

/// One exact parameter row for C-header assembly.
///
/// The declaration type comes from the same sealed binding certificate as the
/// symbol. Consumers may refine it from the render-authorized signature at this
/// exact slot, but never recover a type or identity positionally.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ResolvedParameter {
    pub(crate) slot: u32,
    pub(crate) binding: BindingId,
    pub(crate) symbol: SymbolId,
    pub(crate) width_bits: u32,
    pub(crate) declaration_type: crate::ast::CType,
}

/// Typed failure to obtain one exact renderer identity or machine projection.
///
/// Every variant retains the source-owned identity that failed.  Presentation
/// spellings are deliberately absent: later lowering may propagate these
/// reasons, but it may not recover a value, parameter, stack object, use, or
/// write by searching rendered names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RenderedIdentityRefusal {
    Value {
        value: ValueId,
        reason: ValueRefusal,
    },
    Parameter {
        slot: u32,
        reason: ParameterRefusal,
    },
    StackObject {
        object: ObjectId,
        reason: StackObjectRefusal,
    },
    MachineUse {
        site: UseSite,
        reason: MachineUseRefusal,
    },
    MachineWrite {
        inst: InstId,
        reason: MachineWriteRefusal,
    },
    MissingBinding {
        binding: BindingId,
    },
    MissingValueDisposition {
        value: ValueId,
    },
    MissingParameterDisposition {
        slot: u32,
    },
    MissingStackDisposition {
        object: ObjectId,
    },
    MissingUseDisposition {
        site: UseSite,
    },
    MissingWriteDisposition {
        inst: InstId,
    },
    /// A later consumer retained only layout arithmetic, not the source-owned
    /// stack object whose binding would authorize an identifier.
    MissingStackObjectOrigin {
        offset: i64,
    },
}

/// Failure to project one sealed binding plan into the identifier table used
/// by a single native rendering.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BindingNameResolutionError {
    Source(BindingPlanSourceMismatch),
    ConflictingCertifiedRoles(BindingId),
}

/// Convert one upstream presentation hint into a C identifier before minting.
///
/// This is deliberately a spelling projection, not an identity lookup. The
/// binding plan already decided which program variable exists; sanitizing its
/// hint here keeps initial presentation under the same resolver and leaves the
/// symbol table responsible only for deterministic spelling collisions.
fn c_identifier_for_presentation(hint: &str) -> String {
    let mut identifier = hint
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
        .collect::<String>();
    if identifier.starts_with(|ch: char| ch.is_ascii_digit()) {
        identifier.insert(0, '_');
    }
    if identifier.is_empty() {
        identifier.push('_');
    }
    identifier
}

/// Best source-owned presentation for one certified parameter slot.
///
/// Slot identity is supplied by `BindingRole::Parameter`; these strings can
/// only improve how that already-proven variable is printed. A render-authorized
/// signature is more specific than the source display-name snapshot, and a
/// generic signature placeholder yields to the snapshot.
fn source_parameter_presentation<'a>(
    source_owned: &'a SourceOwnedFunctionFacts,
    slot: u32,
    plan_hint: Option<&'a str>,
) -> Option<&'a str> {
    let Ok(slot) = usize::try_from(slot) else {
        return plan_hint;
    };
    let signature_name = source_owned
        .report()
        .type_facts()
        .render_authorized_signature()
        .and_then(|signature| signature.params.get(slot))
        .map(|parameter| parameter.name.as_str());
    preferred_parameter_presentation(
        signature_name,
        source_owned.report().display_names().parameter(slot),
        plan_hint,
    )
}

fn preferred_parameter_presentation<'a>(
    signature_name: Option<&'a str>,
    display_name: Option<&'a str>,
    plan_hint: Option<&'a str>,
) -> Option<&'a str> {
    signature_name
        .filter(|name| !r2types::is_generic_arg_name(name))
        .or(display_name)
        .or(plan_hint)
}

/// The only projection from [`BindingId`] to a rendered program-variable
/// identity.
///
/// The vectors are dense and immutable after construction. Presentation
/// renames mutate the referenced [`SymbolTable`] entry, so every use of a
/// binding observes the rename without rebuilding an SSA-name map. Whether
/// that symbol is a parameter, a function local, a lexical declaration, or
/// refused is deliberately not stored here; placement is derived later from
/// the sealed region tree.
#[derive(Debug)]
pub(crate) struct BindingNameResolution {
    authority: SsaArtifactAuthority,
    plan: Rc<BindingPlan>,
    symbols: Rc<RefCell<SymbolTable>>,
    by_binding: Box<[SymbolId]>,
}

impl BindingNameResolution {
    pub(crate) fn build(
        source_owned: &SourceOwnedFunctionFacts,
        plan: Rc<BindingPlan>,
        symbols: Rc<RefCell<SymbolTable>>,
    ) -> Result<Self, BindingNameResolutionError> {
        let source = source_owned.source();
        plan.validate_source(source)
            .map_err(BindingNameResolutionError::Source)?;

        let mut by_binding = Vec::with_capacity(plan.binding_count());
        for (binding_id, binding) in plan.bindings() {
            let role = match plan.binding_role(binding_id) {
                Some(BindingRole::Parameter { slot }) => SymbolRole::Parameter(slot),
                Some(BindingRole::StackObject { object }) => {
                    let entity = r2ssa::SemanticId::StackSlot(object);
                    match source_owned
                        .report()
                        .render()
                        .and_then(|render| render.certified_entities.get(&entity))
                    {
                        Some(r2types::CertifiedEntity::StackSlot { offset, .. }) => {
                            SymbolRole::StackLocal(*offset)
                        }
                        _ => {
                            return Err(BindingNameResolutionError::ConflictingCertifiedRoles(
                                binding_id,
                            ));
                        }
                    }
                }
                Some(BindingRole::Local) => SymbolRole::Carrier,
                None => {
                    return Err(BindingNameResolutionError::ConflictingCertifiedRoles(
                        binding_id,
                    ));
                }
            };
            let presentation = match role {
                SymbolRole::Parameter(slot) => source_parameter_presentation(
                    source_owned,
                    slot,
                    binding.presentation_name_hint(),
                ),
                SymbolRole::StackLocal(_) | SymbolRole::Carrier => binding.presentation_name_hint(),
            }
            .map(c_identifier_for_presentation)
            .unwrap_or_else(|| format!("binding_{}", binding_id.index()));
            let symbol = symbols.borrow_mut().reserve_binding(
                presentation,
                binding.declaration_type().clone(),
                role,
            );
            by_binding.push(symbol);
        }

        Ok(Self {
            authority: source.authority().clone(),
            plan,
            symbols,
            by_binding: by_binding.into_boxed_slice(),
        })
    }

    pub(crate) fn symbol_for_binding(&self, binding: BindingId) -> Option<SymbolId> {
        self.by_binding.get(binding.index()).copied()
    }

    /// Whether this exact symbol was minted from one sealed renderer binding.
    ///
    /// Consumers use the `SymbolId`, never its current presentation spelling,
    /// when they need proof that an existing assignment target is a program
    /// variable authorized by the binding plan.
    pub(crate) fn authorizes_program_variable(&self, symbol: SymbolId) -> bool {
        self.by_binding.contains(&symbol)
    }

    /// Exact parameter answers in ascending source ABI slot order.
    ///
    /// Refused slots stay in the iterator as typed errors. Consumers building a
    /// C header therefore cannot skip an unsupported parameter and shift every
    /// later slot into the wrong position.
    pub(crate) fn parameters(
        &self,
    ) -> impl ExactSizeIterator<Item = Result<ResolvedParameter, RenderedIdentityRefusal>> + '_
    {
        self.plan
            .parameters
            .iter()
            .enumerate()
            .map(move |(slot, disposition)| {
                let slot = u32::try_from(slot)
                    .expect("sealed parameter domain fits the source ABI slot domain");
                match *disposition {
                    None => Err(RenderedIdentityRefusal::MissingParameterDisposition { slot }),
                    Some(ParameterDisposition::Bound {
                        binding,
                        width_bits,
                    }) => {
                        let symbol = self
                            .symbol_for_binding(binding)
                            .ok_or(RenderedIdentityRefusal::MissingBinding { binding })?;
                        let declaration_type = self
                            .plan
                            .binding(binding)
                            .ok_or(RenderedIdentityRefusal::MissingBinding { binding })?
                            .declaration_type()
                            .clone();
                        Ok(ResolvedParameter {
                            slot,
                            binding,
                            symbol,
                            width_bits,
                            declaration_type,
                        })
                    }
                    Some(ParameterDisposition::Refused { reason }) => {
                        Err(RenderedIdentityRefusal::Parameter { slot, reason })
                    }
                }
            })
    }

    pub(crate) const fn plan(&self) -> &Rc<BindingPlan> {
        &self.plan
    }

    pub(crate) fn binding_is_externally_declared(&self, binding: BindingId) -> Option<bool> {
        self.plan.binding_is_externally_declared(binding)
    }

    /// Resolve one plan-owned inline expression without exposing the plan.
    pub(crate) fn inline_expr(&self, expr: MachineExprId) -> Option<&r2ssa::MachineExpr> {
        self.plan.machine_projection().expr(expr)
    }

    /// Resolve one exact write projection through the sealed plan. As with
    /// uses, register geometry remains owned by the source-backed machine
    /// projection rather than being reconstructed from a rendered name.
    pub(crate) fn write_disposition(
        &self,
        inst: r2ssa::InstId,
    ) -> Option<&r2ssa::MachineWriteDisposition> {
        self.plan.write_disposition(inst)
    }

    /// Require the exact sealed answer for one SSA value.
    ///
    /// Inline and elided values are successful answers: neither authorizes a C
    /// program variable, but both are complete plan dispositions.  Only an
    /// upstream refusal or an absent dense cell fails this query.
    pub(crate) fn require_value(
        &self,
        value: ValueId,
    ) -> Result<PlannedValueSymbol, RenderedIdentityRefusal> {
        match self.plan.disposition(value) {
            Some(ValueDisposition::Bound { binding }) => self
                .symbol_for_binding(*binding)
                .map(PlannedValueSymbol::Bound)
                .ok_or(RenderedIdentityRefusal::MissingBinding { binding: *binding }),
            Some(ValueDisposition::Inline { expr, .. }) => Ok(PlannedValueSymbol::Inline(*expr)),
            Some(ValueDisposition::Elided { reason, .. }) => {
                Ok(PlannedValueSymbol::Elided(*reason))
            }
            Some(ValueDisposition::Refused { reason }) => Err(RenderedIdentityRefusal::Value {
                value,
                reason: *reason,
            }),
            None => Err(RenderedIdentityRefusal::MissingValueDisposition { value }),
        }
    }

    /// Require one exact certified ABI-parameter slot.
    pub(crate) fn require_parameter_slot(
        &self,
        slot: u32,
    ) -> Result<PlannedParameterSymbol, RenderedIdentityRefusal> {
        match self.plan.parameter_disposition(slot) {
            Some(ParameterDisposition::Bound {
                binding,
                width_bits,
            }) => self
                .symbol_for_binding(binding)
                .map(|symbol| PlannedParameterSymbol::Bound { symbol, width_bits })
                .ok_or(RenderedIdentityRefusal::MissingBinding { binding }),
            Some(ParameterDisposition::Refused { reason }) => {
                Err(RenderedIdentityRefusal::Parameter { slot, reason })
            }
            None => Err(RenderedIdentityRefusal::MissingParameterDisposition { slot }),
        }
    }

    /// Require one exact source-owned stack object without reconstructing it
    /// from an offset or a local spelling.
    pub(crate) fn require_stack(
        &self,
        object: ObjectId,
    ) -> Result<PlannedStackSymbol, RenderedIdentityRefusal> {
        match self.plan.stack_object_disposition(object) {
            Some(StackObjectDisposition::Bound { binding }) => self
                .symbol_for_binding(binding)
                .map(PlannedStackSymbol::Bound)
                .ok_or(RenderedIdentityRefusal::MissingBinding { binding }),
            Some(StackObjectDisposition::Refused { reason }) => {
                Err(RenderedIdentityRefusal::StackObject { object, reason })
            }
            None => Err(RenderedIdentityRefusal::MissingStackDisposition { object }),
        }
    }

    /// Require the canonical disposition for one exact graph use.
    ///
    /// The successful reference points directly into the plan-owned upstream
    /// [`r2ssa::MachineProjection`].  No use slice or contextual memory-address
    /// certificate is copied into renderer storage.
    pub(crate) fn require_use(
        &self,
        site: UseSite,
    ) -> Result<&MachineUseDisposition, RenderedIdentityRefusal> {
        match self.plan.machine_projection().use_disposition(site) {
            Some(
                disposition @ (MachineUseDisposition::Exact(_)
                | MachineUseDisposition::MemoryAddress(_)),
            ) => Ok(disposition),
            Some(MachineUseDisposition::Refused(reason)) => {
                Err(RenderedIdentityRefusal::MachineUse {
                    site,
                    reason: *reason,
                })
            }
            None => Err(RenderedIdentityRefusal::MissingUseDisposition { site }),
        }
    }

    /// Require the canonical disposition for one exact graph definition.
    ///
    /// As with uses, this returns a reference to the sealed machine projection
    /// and only copies a typed refusal reason when projection was refused.
    pub(crate) fn require_write(
        &self,
        inst: InstId,
    ) -> Result<&MachineWriteDisposition, RenderedIdentityRefusal> {
        match self.plan.machine_projection().write_disposition(inst) {
            Some(disposition @ MachineWriteDisposition::Exact(_)) => Ok(disposition),
            Some(MachineWriteDisposition::Refused(reason)) => {
                Err(RenderedIdentityRefusal::MachineWrite {
                    inst,
                    reason: *reason,
                })
            }
            None => Err(RenderedIdentityRefusal::MissingWriteDisposition { inst }),
        }
    }

    pub(crate) fn symbol_for_value(&self, value: ValueId) -> Option<SymbolId> {
        match self.resolve_value(value) {
            PlannedValueSymbol::Bound(symbol) => Some(symbol),
            PlannedValueSymbol::Inline(_)
            | PlannedValueSymbol::Elided(_)
            | PlannedValueSymbol::Refused(_)
            | PlannedValueSymbol::Absent => None,
        }
    }

    /// Resolve one dense `ValueId` without recovering identity from an SSA
    /// variable or presentation name.
    pub(crate) fn resolve_value(&self, value: ValueId) -> PlannedValueSymbol {
        match self.plan.disposition(value) {
            Some(ValueDisposition::Bound { binding }) => self
                .symbol_for_binding(*binding)
                .map_or(PlannedValueSymbol::Absent, PlannedValueSymbol::Bound),
            Some(ValueDisposition::Inline { expr, .. }) => PlannedValueSymbol::Inline(*expr),
            Some(ValueDisposition::Elided { reason, .. }) => PlannedValueSymbol::Elided(*reason),
            Some(ValueDisposition::Refused { reason }) => PlannedValueSymbol::Refused(*reason),
            None => PlannedValueSymbol::Absent,
        }
    }

    /// The sealed disposition for one exact SSA value.
    ///
    /// This delegates to the plan's dense `ValueId` table. Consumers that must
    /// distinguish "there is no planned value here" from an authoritative
    /// inline/elide/refuse answer use this instead of treating
    /// [`symbol_for_value`](Self::symbol_for_value) as a boolean.
    pub(crate) fn disposition_for_value(&self, value: ValueId) -> Option<&ValueDisposition> {
        self.plan.disposition(value)
    }

    pub(crate) fn validates_artifact(&self, source: &r2ssa::SsaArtifact) -> bool {
        self.authority == *source.authority()
    }

    pub(crate) fn owns_symbol_table(&self, symbols: &RefCell<SymbolTable>) -> bool {
        std::ptr::eq(self.symbols.as_ref(), symbols)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use r2il::{
        AddressSpace, ArchSpec, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef,
        RegisterProjection, RegisterProjectionDisposition, RegisterStorage, Varnode,
    };
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceFunctionInterface,
        SourceFunctionReturn, SsaArtifact,
    };

    use super::*;

    #[test]
    fn presentation_hints_are_sanitized_before_symbol_minting() {
        assert_eq!(c_identifier_for_presentation("tmp:11f80"), "tmp_11f80");
        assert_eq!(c_identifier_for_presentation("7th-value"), "_7th_value");
        assert_eq!(c_identifier_for_presentation(""), "_");
        assert_eq!(c_identifier_for_presentation("already_c"), "already_c");
    }

    #[test]
    fn parameter_presentation_priority_is_source_owned_and_deterministic() {
        assert_eq!(
            preferred_parameter_presentation(Some("length"), Some("count"), Some("rdi")),
            Some("length")
        );
        assert_eq!(
            preferred_parameter_presentation(Some("arg0"), Some("count"), Some("rdi")),
            Some("count")
        );
        assert_eq!(
            preferred_parameter_presentation(Some("arg0"), None, Some("rdi")),
            Some("rdi")
        );
    }

    fn source_owned() -> r2types::SourceOwnedFunctionFacts {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(1, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x20, 8),
            src: Varnode::unique(0x10, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::unique(0x20, 8),
        });
        source_owned_from_block(block, 8)
    }

    fn source_owned_using_parameter(width_bytes: u32) -> r2types::SourceOwnedFunctionFacts {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, width_bytes),
            src: Varnode::register(0x38, width_bytes),
        });
        block.push(R2ILOp::Return {
            target: Varnode::unique(0x10, width_bytes),
        });
        source_owned_from_block(block, width_bytes)
    }

    fn source_owned_from_block(
        block: R2ILBlock,
        parameter_width: u32,
    ) -> r2types::SourceOwnedFunctionFacts {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_space(AddressSpace::ram(8));
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch.add_register(RegisterDef::new("RIP", 0x30, 8));
        arch.add_register(RegisterDef::new("RDI", 0x38, parameter_width));
        arch.register_projections = [(0, 8), (0x28, 8), (0x30, 8), (0x38, parameter_width)]
            .into_iter()
            .map(|(offset, size)| RegisterProjection {
                written: RegisterStorage { offset, size },
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: RegisterStorage { offset, size },
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: u64::from(size) * 8,
                    },
                },
            })
            .collect();
        let storage = |offset| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = SourceFunctionInterface::new_exact(
            b"binding-name-resolution".to_vec(),
            "sysv64",
            [SourceAbiParameterSpec::new(
                0,
                CanonicalStorageId {
                    space: CanonicalStorageSpace::Register,
                    offset: 0x38,
                    size: parameter_width,
                },
            )],
            SourceFunctionReturn::Register {
                storage: storage(0),
            },
            std::iter::empty(),
        )
        .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
        .expect("interface");
        let source = Arc::new(
            SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
                .expect("SSA artifact"),
        );
        let request = r2types::TypeWritebackAnalysisRequest::new(
            source,
            r2types::ParsedExternalContext::default(),
        )
        .expect("request");
        r2types::build_source_owned_type_writeback_analysis(request)
            .expect("facts")
            .finalize_for_decompile(r2types::DecompileFinalization {
                kind: r2types::DecompileRouteKind::Standard,
                reason: "binding name resolution test".to_string(),
                fallback_comment: None,
            })
            .expect("finalized facts")
    }

    #[test]
    fn one_binding_mints_one_symbol_for_every_member() {
        let source = source_owned();
        let plan = BindingPlan::build_shadow(&source).expect("plan");
        let symbols = Rc::new(RefCell::new(SymbolTable::new()));
        let resolution =
            BindingNameResolution::build(&source, Rc::new(plan.clone()), Rc::clone(&symbols))
                .expect("resolution");

        for value in &source.source().graph().values {
            match plan.disposition(value.id) {
                Some(ValueDisposition::Bound { binding }) => {
                    assert_eq!(
                        resolution.symbol_for_value(value.id),
                        resolution.symbol_for_binding(*binding)
                    );
                }
                Some(ValueDisposition::Inline { .. }) => {
                    assert_eq!(resolution.symbol_for_value(value.id), None);
                }
                other => panic!("unexpected disposition: {other:?}"),
            }
        }
    }

    #[test]
    fn presentation_rename_preserves_binding_identity() {
        let source = source_owned();
        let plan = BindingPlan::build_shadow(&source).expect("plan");
        let symbols = Rc::new(RefCell::new(SymbolTable::new()));
        let resolution =
            BindingNameResolution::build(&source, Rc::new(plan.clone()), Rc::clone(&symbols))
                .expect("resolution");
        let (binding, _) = plan.bindings().next().expect("binding");
        let symbol = resolution.symbol_for_binding(binding).expect("symbol");

        symbols.borrow_mut().rename(symbol, "accumulator");

        let member = source
            .source()
            .graph()
            .values
            .iter()
            .find(|value| plan.disposition(value.id) == Some(&ValueDisposition::Bound { binding }))
            .expect("member");
        assert_eq!(resolution.symbol_for_value(member.id), Some(symbol));
        assert_eq!(symbols.borrow().name(symbol), "accumulator");
    }

    #[test]
    fn resolver_rejects_foreign_source_and_symbol_table_pairing() {
        let source = source_owned();
        let foreign = source_owned();
        let plan = BindingPlan::build_shadow(&source).expect("plan");
        assert!(matches!(
            BindingNameResolution::build(
                &foreign,
                Rc::new(plan.clone()),
                Rc::new(RefCell::new(SymbolTable::new()))
            ),
            Err(BindingNameResolutionError::Source(
                BindingPlanSourceMismatch::Authority
            ))
        ));
        let symbols = Rc::new(RefCell::new(SymbolTable::new()));
        let resolution = BindingNameResolution::build(&source, Rc::new(plan), Rc::clone(&symbols))
            .expect("resolution");
        let foreign_symbols = RefCell::new(SymbolTable::new());

        assert!(resolution.validates_artifact(source.source()));
        assert!(!resolution.validates_artifact(foreign.source()));
        assert!(resolution.owns_symbol_table(symbols.as_ref()));
        assert!(!resolution.owns_symbol_table(&foreign_symbols));
    }

    #[test]
    fn unused_certified_parameter_gets_an_exact_external_binding() {
        let source = source_owned();
        assert_eq!(
            source
                .report()
                .render()
                .expect("render facts")
                .parameter_values(0)
                .count(),
            0,
            "fixture parameter must have no entry ValueId"
        );
        let plan = BindingPlan::build_shadow(&source).expect("unused parameter plan");
        let ParameterDisposition::Bound {
            binding,
            width_bits,
        } = plan
            .parameter_disposition(0)
            .expect("slot zero disposition")
        else {
            panic!("unused certified parameter was refused")
        };
        assert_eq!(width_bits, 64);
        assert_eq!(
            plan.binding_role(binding),
            Some(BindingRole::Parameter { slot: 0 })
        );
        assert_eq!(plan.binding_is_externally_declared(binding), Some(true));
        assert!(source.source().graph().values.iter().all(|value| {
            plan.disposition(value.id) != Some(&ValueDisposition::Bound { binding })
        }));

        let resolution = BindingNameResolution::build(
            &source,
            Rc::new(plan),
            Rc::new(RefCell::new(SymbolTable::new())),
        )
        .expect("unused parameter resolution");
        let PlannedParameterSymbol::Bound {
            symbol,
            width_bits: resolved_width,
        } = resolution
            .require_parameter_slot(0)
            .expect("parameter symbol");
        assert_eq!(resolved_width, 64);
        assert_eq!(
            resolution.require_parameter_slot(7),
            Err(RenderedIdentityRefusal::MissingParameterDisposition { slot: 7 })
        );
        assert_eq!(
            resolution.parameters().collect::<Vec<_>>(),
            vec![Ok(ResolvedParameter {
                slot: 0,
                binding,
                symbol,
                width_bits: 64,
                declaration_type: resolution
                    .plan()
                    .binding(binding)
                    .expect("parameter binding")
                    .declaration_type()
                    .clone(),
            })]
        );
    }

    #[test]
    fn value_backed_parameter_reuses_its_certified_binding() {
        let source = source_owned_using_parameter(8);
        let entry_values = source
            .report()
            .render()
            .expect("render facts")
            .parameter_values(0)
            .collect::<Vec<_>>();
        assert!(
            !entry_values.is_empty(),
            "fixture must certify an entry value"
        );
        let plan = BindingPlan::build_shadow(&source).expect("value-backed parameter plan");
        let ParameterDisposition::Bound { binding, .. } = plan
            .parameter_disposition(0)
            .expect("slot zero disposition")
        else {
            panic!("value-backed parameter was refused")
        };
        assert!(entry_values.iter().all(|value| {
            plan.disposition(*value) == Some(&ValueDisposition::Bound { binding })
        }));
        assert_eq!(
            plan.binding(binding)
                .expect("reused binding")
                .certificate
                .sources
                .iter()
                .filter(|source| {
                    **source
                        == super::super::BindingCertificateSource::CertifiedEntity(
                            r2ssa::SemanticId::Parameter(0),
                        )
                })
                .count(),
            1
        );
    }

    #[test]
    fn unsupported_parameter_width_is_refused_and_conflicting_roles_are_rejected() {
        let source = source_owned_using_parameter(3);
        let plan = BindingPlan::build_shadow(&source).expect("refusing parameter plan");
        assert_eq!(
            plan.parameter_disposition(0),
            Some(ParameterDisposition::Refused {
                reason: ParameterRefusal::UnsupportedWidth {
                    entity: r2ssa::SemanticId::Parameter(0),
                    slot: 0,
                    width_bits: 24,
                }
            })
        );
        let resolution = BindingNameResolution::build(
            &source,
            Rc::new(plan),
            Rc::new(RefCell::new(SymbolTable::new())),
        )
        .expect("refusing parameter resolution");
        assert_eq!(
            resolution.require_parameter_slot(0),
            Err(RenderedIdentityRefusal::Parameter {
                slot: 0,
                reason: ParameterRefusal::UnsupportedWidth {
                    entity: r2ssa::SemanticId::Parameter(0),
                    slot: 0,
                    width_bits: 24,
                }
            })
        );

        let conflict_source = source_owned();
        let mut conflict_plan =
            BindingPlan::build_shadow(&conflict_source).expect("conflict fixture plan");
        let binding = conflict_plan.bindings().next().expect("fixture binding").0;
        conflict_plan.bindings[binding.index()].certificate.sources = Box::new([
            super::super::BindingCertificateSource::CertifiedEntity(r2ssa::SemanticId::Parameter(
                0,
            )),
            super::super::BindingCertificateSource::CertifiedEntity(r2ssa::SemanticId::Parameter(
                1,
            )),
        ]);
        assert_eq!(conflict_plan.binding_role(binding), None);
        assert!(matches!(
            BindingNameResolution::build(
                &conflict_source,
                Rc::new(conflict_plan),
                Rc::new(RefCell::new(SymbolTable::new()))
            ),
            Err(BindingNameResolutionError::ConflictingCertifiedRoles(conflict))
                if conflict == binding
        ));
    }

    #[test]
    fn value_resolution_keeps_every_planned_answer_distinct() {
        let source = source_owned();
        let plan = BindingPlan::build_shadow(&source).expect("plan");
        let symbols = Rc::new(RefCell::new(SymbolTable::new()));
        let resolution =
            BindingNameResolution::build(&source, Rc::new(plan.clone()), Rc::clone(&symbols))
                .expect("resolution");

        let bound = source
            .source()
            .graph()
            .values
            .iter()
            .find_map(|value| match plan.disposition(value.id) {
                Some(ValueDisposition::Bound { binding }) => Some((value.id, *binding)),
                _ => None,
            })
            .expect("bound value");
        let inline = source
            .source()
            .graph()
            .values
            .iter()
            .find_map(|value| match plan.disposition(value.id) {
                Some(ValueDisposition::Inline { expr, .. }) => Some((value.id, *expr)),
                _ => None,
            })
            .expect("inline value");
        assert_eq!(
            resolution.resolve_value(bound.0),
            PlannedValueSymbol::Bound(
                resolution
                    .symbol_for_binding(bound.1)
                    .expect("bound symbol")
            )
        );
        assert_eq!(
            resolution.require_value(bound.0),
            Ok(PlannedValueSymbol::Bound(
                resolution
                    .symbol_for_binding(bound.1)
                    .expect("bound symbol")
            ))
        );
        assert_eq!(
            resolution.resolve_value(inline.0),
            PlannedValueSymbol::Inline(inline.1)
        );
        assert_eq!(
            resolution.require_value(inline.0),
            Ok(PlannedValueSymbol::Inline(inline.1))
        );
        assert_eq!(
            resolution.resolve_value(ValueId(u32::MAX)),
            PlannedValueSymbol::Absent
        );
        assert_eq!(
            resolution.require_value(ValueId(u32::MAX)),
            Err(RenderedIdentityRefusal::MissingValueDisposition {
                value: ValueId(u32::MAX)
            })
        );

        let mut elided_plan = plan.clone();
        elided_plan.replace_value_disposition_for_shadow_test(
            bound.0,
            ValueDisposition::Elided {
                reason: r2ssa::ledger::ElisionReason::DeadUnusedTemporary,
                proof: crate::binding_plan::ValueElisionProof {
                    authority: source.source().authority().clone(),
                    value: bound.0,
                },
            },
        );
        let elided = BindingNameResolution::build(
            &source,
            Rc::new(elided_plan),
            Rc::new(RefCell::new(SymbolTable::new())),
        )
        .expect("elided resolution");
        assert_eq!(
            elided.resolve_value(bound.0),
            PlannedValueSymbol::Elided(r2ssa::ledger::ElisionReason::DeadUnusedTemporary)
        );
        assert_eq!(
            elided.require_value(bound.0),
            Ok(PlannedValueSymbol::Elided(
                r2ssa::ledger::ElisionReason::DeadUnusedTemporary
            ))
        );

        let refusal = ValueRefusal::MissingBindingCertificate { value: bound.0 };
        let mut refused_plan = plan;
        refused_plan.replace_value_disposition_for_shadow_test(
            bound.0,
            ValueDisposition::Refused { reason: refusal },
        );
        let refused = BindingNameResolution::build(
            &source,
            Rc::new(refused_plan),
            Rc::new(RefCell::new(SymbolTable::new())),
        )
        .expect("refused resolution");
        assert_eq!(
            refused.resolve_value(bound.0),
            PlannedValueSymbol::Refused(refusal)
        );
        assert_eq!(
            refused.require_value(bound.0),
            Err(RenderedIdentityRefusal::Value {
                value: bound.0,
                reason: refusal
            })
        );
    }

    #[test]
    fn stack_require_keeps_refusal_and_absence_distinct() {
        let source = source_owned();
        let mut plan = BindingPlan::build_shadow(&source).expect("plan");
        let refused_object = ObjectId(7);
        let refusal = StackObjectRefusal::MissingWidth {
            object: refused_object,
        };
        plan.stack_objects.insert(
            refused_object,
            StackObjectDisposition::Refused { reason: refusal },
        );
        let resolution = BindingNameResolution::build(
            &source,
            Rc::new(plan),
            Rc::new(RefCell::new(SymbolTable::new())),
        )
        .expect("resolution");
        assert_eq!(
            resolution.require_stack(refused_object),
            Err(RenderedIdentityRefusal::StackObject {
                object: refused_object,
                reason: refusal
            })
        );
        assert_eq!(
            resolution.require_stack(ObjectId(u32::MAX)),
            Err(RenderedIdentityRefusal::MissingStackDisposition {
                object: ObjectId(u32::MAX)
            })
        );
    }
}
