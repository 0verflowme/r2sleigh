use std::cell::RefCell;
use std::rc::Rc;

use r2ssa::{SsaArtifactAuthority, ValueId};
use r2types::SourceOwnedFunctionFacts;

use super::{BindingId, BindingPlan, BindingPlanSourceMismatch, ValueDisposition};
use crate::symbol::{SymbolId, SymbolRole, SymbolTable};

/// Failure to project one sealed binding plan into the identifier table used
/// by a single native rendering.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BindingNameResolutionError {
    Source(BindingPlanSourceMismatch),
    MissingBinding(BindingId),
    ConflictingCertifiedRoles(BindingId),
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
            let mut roles = binding
                .certificate
                .sources
                .iter()
                .filter_map(|source| {
                    let super::BindingCertificateSource::CertifiedEntity(id) = source else {
                        return None;
                    };
                    match source_owned.report().render()?.certified_entities.get(id)? {
                        r2types::CertifiedEntity::Parameter { slot, .. } => {
                            Some(SymbolRole::Parameter(*slot))
                        }
                        r2types::CertifiedEntity::StackSlot { offset, .. } => {
                            Some(SymbolRole::StackLocal(*offset))
                        }
                        r2types::CertifiedEntity::LoopCarrier { .. } => None,
                    }
                })
                .collect::<Vec<_>>();
            roles.sort_by_key(|role| match role {
                SymbolRole::Parameter(slot) => (0_u8, i64::from(*slot)),
                SymbolRole::StackLocal(offset) => (1_u8, *offset),
                SymbolRole::Carrier => (2_u8, 0),
            });
            roles.dedup();
            if roles.len() > 1 {
                return Err(BindingNameResolutionError::ConflictingCertifiedRoles(
                    binding_id,
                ));
            }
            let role = roles.pop().unwrap_or(SymbolRole::Carrier);
            let presentation = binding
                .presentation_name_hint()
                .map(ToOwned::to_owned)
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

    pub(crate) fn symbol_for_value(&self, value: ValueId) -> Option<SymbolId> {
        let ValueDisposition::Bound { binding } = self.plan.disposition(value)? else {
            return None;
        };
        self.symbol_for_binding(*binding)
    }

    pub(crate) fn name_for_value(&self, value: ValueId) -> Option<String> {
        let symbol = self.symbol_for_value(value)?;
        Some(self.symbols.borrow().name(symbol).to_string())
    }

    pub(crate) fn symbol_for_stack_object(&self, object: r2ssa::ObjectId) -> Option<SymbolId> {
        let super::StackObjectDisposition::Bound { binding } =
            self.plan.stack_object_disposition(object)?
        else {
            return None;
        };
        self.symbol_for_binding(binding)
    }

    pub(crate) fn name_for_stack_object(&self, object: r2ssa::ObjectId) -> Option<String> {
        let symbol = self.symbol_for_stack_object(object)?;
        Some(self.symbols.borrow().name(symbol).to_string())
    }

    pub(crate) fn symbols(&self) -> &Rc<RefCell<SymbolTable>> {
        &self.symbols
    }

    pub(crate) fn validate_source(&self, source: &SourceOwnedFunctionFacts) -> bool {
        self.authority == *source.source().authority()
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
        CanonicalStorageId, CanonicalStorageSpace, SourceFunctionInterface, SourceFunctionReturn,
        SsaArtifact,
    };

    use super::*;

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
        let mut arch = ArchSpec::new("x86-64");
        arch.add_space(AddressSpace::ram(8));
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch.add_register(RegisterDef::new("RIP", 0x30, 8));
        arch.register_projections = [(0, 8), (0x28, 8), (0x30, 8)]
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
            std::iter::empty(),
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
        assert_eq!(
            resolution.name_for_value(member.id).as_deref(),
            Some("accumulator")
        );
        assert!(resolution.validate_source(&source));
    }

    #[test]
    fn resolver_rejects_foreign_source_and_symbol_table_pairing() {
        let source = source_owned();
        let foreign = source_owned();
        let plan = BindingPlan::build_shadow(&source).expect("plan");
        let symbols = Rc::new(RefCell::new(SymbolTable::new()));
        let resolution =
            BindingNameResolution::build(&source, Rc::new(plan), Rc::clone(&symbols))
                .expect("resolution");
        let foreign_symbols = RefCell::new(SymbolTable::new());

        assert!(resolution.validates_artifact(source.source()));
        assert!(!resolution.validates_artifact(foreign.source()));
        assert!(resolution.owns_symbol_table(symbols.as_ref()));
        assert!(!resolution.owns_symbol_table(&foreign_symbols));
    }
}
