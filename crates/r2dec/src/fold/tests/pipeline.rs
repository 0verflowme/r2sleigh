#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        collections::{BTreeMap, BTreeSet, HashMap, HashSet},
        ops::Deref,
        sync::Arc,
    };

    use crate::analysis::PtrArith;
    use crate::fold::context::{EffectRenderProofKind, empty_function_facts};
    use crate::{
        FoldArchConfig, FoldInputs,
        analysis::{
            CallOwner, CallOwnerKind, CallOwnershipFact, CallSiteId, PassEnv, PreparedSemanticView,
            ScalarValue, SemanticValue, StackSlotProvenance, StackSlotValueKind,
        },
    };
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }
    use r2types::{
        CalleeArgEffect, CalleeFact, CalleeReturnRelation, ExternalField, ExternalStackBase,
        ExternalStackVarSpec, ExternalStruct, ExternalTypeDb, Signedness, SolvedTypes,
        SolverDiagnostics, StackSlotKey, StructShape, TypeArena, TypeId, TypeOracle,
        VisibleBinding, VisibleBindingKind,
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
        arch.add_register(RegisterDef::new("RDX", 0x38, 8));
        arch.add_register(RegisterDef::new("RCX", 0x40, 8));
        arch.add_register(RegisterDef::new("R8", 0x48, 8));
        arch.add_register(RegisterDef::new("R9", 0x50, 8));
        arch.add_register(RegisterDef::new("RBP", 0x20, 8));
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch.add_register(RegisterDef::new("RIP", 0x30, 8));
        arch
    }

    fn make_test_arch_aarch64_kernel_regs() -> ArchSpec {
        let mut arch = ArchSpec::new("aarch64");
        arch.add_register(RegisterDef::new("x0", 0x4000, 8));
        arch.add_register(RegisterDef::sub("w0", 0x4000, 4, "x0"));
        for index in 1..8 {
            let offset = 0x4000 + index * 8;
            arch.add_register(RegisterDef::new(format!("x{index}"), offset, 8));
            arch.add_register(RegisterDef::sub(
                format!("w{index}"),
                offset,
                4,
                format!("x{index}"),
            ));
        }
        arch.add_register(RegisterDef::new("x8", 0x4040, 8));
        arch.add_register(RegisterDef::sub("w8", 0x4040, 4, "x8"));
        arch.add_register(RegisterDef::new("x20", 0x40a0, 8));
        arch.add_register(RegisterDef::sub("w20", 0x40a0, 4, "x20"));
        arch.add_register(RegisterDef::new("x30", 0x40f0, 8));
        arch.add_register(RegisterDef::new("sp", 0x4100, 8));
        arch
    }

    struct SourceOwnedPreparedFixture {
        facts: r2types::function_facts::SourceOwnedFunctionFacts,
    }

    impl SourceOwnedPreparedFixture {
        fn new(prepared: r2ssa::SsaArtifact) -> Self {
            Self::new_with_context(prepared, r2types::ParsedExternalContext::default())
        }

        fn new_with_context(
            prepared: r2ssa::SsaArtifact,
            parsed_context: r2types::ParsedExternalContext,
        ) -> Self {
            let source = Arc::new(prepared);
            let request =
                r2types::TypeWritebackAnalysisRequest::new(Arc::clone(&source), parsed_context)
                    .expect("fixture assumptions must match the exact source");
            let analysis = r2types::build_source_owned_type_writeback_analysis(request)
                .expect("fixture must produce source-owned analysis");
            let facts = analysis
                .finalize_for_decompile(r2types::DecompileFinalization {
                    kind: r2types::DecompileRouteKind::Standard,
                    reason: "r2dec fold pipeline source fixture".to_string(),
                    fallback_comment: None,
                })
                .expect("fixture must finalize against its exact source");
            Self { facts }
        }

        fn with_name(self, name: impl Into<String>) -> Self {
            let source = self.facts.shared_source();
            drop(self.facts);
            let prepared = Arc::try_unwrap(source)
                .expect("fixture must retain the only prepared source owner")
                .with_name(name);
            Self::new(prepared)
        }

        fn with_context(self, parsed_context: r2types::ParsedExternalContext) -> Self {
            let source = self.facts.shared_source();
            drop(self.facts);
            let prepared = Arc::try_unwrap(source)
                .expect("fixture must retain the only prepared source owner");
            Self::new_with_context(prepared, parsed_context)
        }

        fn function_facts(&self) -> &r2types::FunctionFacts {
            self.facts.report()
        }
    }

    impl Deref for SourceOwnedPreparedFixture {
        type Target = r2ssa::SsaArtifact;

        fn deref(&self) -> &Self::Target {
            self.facts.source()
        }
    }

    fn source_owned_fixture(prepared: r2ssa::SsaArtifact) -> SourceOwnedPreparedFixture {
        SourceOwnedPreparedFixture::new(prepared)
    }

    fn prepared_from_r2il_blocks(
        blocks: &[R2ILBlock],
        arch: &ArchSpec,
    ) -> SourceOwnedPreparedFixture {
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let (calling_convention, parameter_offsets, return_storage, return_address, stack_pointer) =
            if arch.name.eq_ignore_ascii_case("aarch64") {
                (
                    "aapcs64",
                    (0..8).map(|index| 0x4000 + index * 8).collect::<Vec<_>>(),
                    storage(0x4000),
                    storage(0x40f0),
                    storage(0x4100),
                )
            } else {
                (
                    "sysv64",
                    vec![0x10, 0x18, 0x38, 0x40, 0x48, 0x50],
                    storage(0),
                    storage(0x30),
                    storage(0x28),
                )
            };
        let parameters = parameter_offsets
            .into_iter()
            .enumerate()
            .map(|(index, offset)| {
                r2ssa::SourceAbiParameterSpec::new(index as u32, storage(offset))
            })
            .collect::<Vec<_>>();
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"r2dec-fold-pipeline-source-v1".to_vec(),
            calling_convention,
            parameters,
            r2ssa::SourceFunctionReturn::Register {
                storage: return_storage,
            },
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(return_address))
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("exact source interface");
        source_owned_fixture(
            r2ssa::SsaArtifact::for_decompile_with_interface(blocks, Some(arch), interface)
                .expect("prepared SSA should build"),
        )
    }

    fn prepared_x86_with_stack_slot(
        blocks: &[R2ILBlock],
        arch: &ArchSpec,
        base: r2ssa::StackAddressBase,
        offset: i64,
        size: u32,
    ) -> SourceOwnedPreparedFixture {
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let base_storage = match base {
            r2ssa::StackAddressBase::FramePointer => storage(0x20),
            r2ssa::StackAddressBase::StackPointer => storage(0x28),
        };
        let parameters = [0x10, 0x18, 0x38, 0x40, 0x48, 0x50]
            .into_iter()
            .enumerate()
            .map(|(index, offset)| {
                r2ssa::SourceAbiParameterSpec::new(index as u32, storage(offset))
            })
            .collect::<Vec<_>>();
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"r2dec-fold-pipeline-stack-source-v1".to_vec(),
            "sysv64",
            parameters,
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [r2ssa::SourceStackSlotSpec::new_local(
                base,
                base_storage,
                offset,
                size,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
        .and_then(|interface| {
            if base == r2ssa::StackAddressBase::FramePointer {
                interface.with_frame_pointer_storage(storage(0x20))
            } else {
                Ok(interface)
            }
        })
        .expect("exact stack source interface");
        source_owned_fixture(
            r2ssa::SsaArtifact::for_decompile_with_interface(blocks, Some(arch), interface)
                .expect("prepared stack SSA should build"),
        )
    }

    fn call_arg(expr: CExpr) -> crate::analysis::CallArgBinding {
        let mut binding = crate::analysis::CallArgBinding::from(expr);
        binding.source_var_name = Some(fixture_source_name_for_expr(&binding.arg));
        binding
    }

    fn fixture_source_name_for_expr(arg: &crate::analysis::SemanticCallArg) -> String {
        let seed = match arg {
            crate::analysis::SemanticCallArg::FallbackExpr(expr) => format!("{expr:?}"),
            crate::analysis::SemanticCallArg::StringAddr(addr) => format!("string_{addr:x}"),
            crate::analysis::SemanticCallArg::Semantic(value) => format!("{value:?}"),
        };
        let mut name = String::from("__test_source_");
        for ch in seed.chars().take(96) {
            if ch.is_ascii_alphanumeric() {
                name.push(ch.to_ascii_lowercase());
            } else {
                name.push('_');
            }
        }
        name
    }

    fn fixture_owner_expr_for_arg(
        ctx: &FoldingContext<'_>,
        binding: &crate::analysis::CallArgBinding,
    ) -> CExpr {
        match &binding.arg {
            crate::analysis::SemanticCallArg::FallbackExpr(expr) => expr.clone(),
            crate::analysis::SemanticCallArg::StringAddr(addr) => CExpr::UIntLit(*addr),
            crate::analysis::SemanticCallArg::Semantic(_) => binding
                .source_var_name
                .as_ref()
                .map(|name| ctx.name_ref(name))
                .unwrap_or_else(|| ctx.unresolved_call_arg_expr()),
        }
    }

    fn authorize_call_arg_sources(
        ctx: &mut FoldingContext<'_>,
        args: &[crate::analysis::CallArgBinding],
    ) {
        let symbols = test_table();
        let mut view = ctx
            .inputs
            .prepared_semantic_view
            .cloned()
            .unwrap_or_default();
        for binding in args {
            if let Some(name) = &binding.source_var_name {
                view.owner_expr_by_name
                    .insert(name.clone(), fixture_owner_expr_for_arg(ctx, binding));
            }
        }
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(view)));
    }

    fn insert_authorized_call_args(
        ctx: &mut FoldingContext<'_>,
        source_call: (u64, usize),
        mut args: Vec<crate::analysis::CallArgBinding>,
    ) {
        authorize_call_arg_sources(ctx, &args);
        let argument_values = args
            .iter_mut()
            .enumerate()
            .map(|(index, binding)| {
                let value = binding
                    .source_value_id
                    .unwrap_or(r2ssa::ValueId(10_000 + index as u32));
                binding.source_value_id = Some(value);
                r2types::CallArgumentValueFact { index, value }
            })
            .collect::<Vec<_>>();
        let mut callsite_facts = ctx
            .inputs
            .function_facts
            .callsites()
            .cloned()
            .unwrap_or_default();
        let callsite = r2types::CallsiteKey {
            block_addr: source_call.0,
            op_index: source_call.1,
        };
        callsite_facts.by_callsite.insert(
            callsite,
            r2types::CallsiteArgumentFacts {
                callsite,
                call_site_id: r2ssa::CallSiteId(source_call.1 as u32),
                at: r2ssa::InstId(source_call.1 as u32),
                target: r2ssa::ValueId(9_999),
                direct_target: None,
                argument_values,
                register_argument_locations: Vec::new(),
                stack_argument_locations: Vec::new(),
            },
        );
        install_function_callsite_facts(ctx, callsite_facts);
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert(source_call, args);
    }

    fn install_callsite_resolution(
        ctx: &mut FoldingContext<'_>,
        source_call: (u64, usize),
        target_addr: u64,
        target_name: &str,
        signature: Option<FunctionType>,
    ) {
        let symbols = test_table();
        let typed_names = HashMap::from([(target_addr, target_name.to_string())]);
        let binary_symbols = HashMap::new();
        let callee_facts = if r2types::callee_name_is_import_like(target_name) {
            BTreeMap::from([(
                target_addr,
                minimal_callee_fact_with_linkage(
                    target_addr,
                    target_name,
                    r2types::CalleeLinkage::Imported,
                ),
            )])
        } else {
            BTreeMap::new()
        };
        let known_signatures: HashMap<String, r2types::FunctionType> = signature
            .map(|signature| (target_name.to_string(), signature.into()))
            .into_iter()
            .collect();
        let resolution = r2types::CalleeResolutionFacts::from_direct_call_targets(
            [(
                r2types::CallsiteKey {
                    block_addr: source_call.0,
                    op_index: source_call.1,
                },
                target_addr,
            )],
            &r2types::CalleeIdentityContext {
                function_names: &typed_names,
                symbols: &binary_symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_signatures,
            },
        );
        mutate_function_facts(ctx, |function_facts| {
            if !callee_facts.is_empty() {
                let mut type_facts = function_facts.type_facts().clone();
                type_facts.callee_facts = callee_facts;
                function_facts.replace_type_facts(type_facts);
            }
            function_facts.set_callee_resolution(resolution);
        });
    }

    fn install_indirect_callsite_identity(
        ctx: &mut FoldingContext<'_>,
        source_call: (u64, usize),
        target_name: &str,
        signature: Option<FunctionType>,
    ) {
        let key = r2types::CalleeIdentityKey::IndirectSite(r2types::CallsiteKey {
            block_addr: source_call.0,
            op_index: source_call.1,
        });
        let signatures: HashMap<String, r2types::FunctionType> = signature
            .map(|signature| (target_name.to_string(), signature.into()))
            .into_iter()
            .collect();
        let mut identity =
            r2types::CalleeIdentity::from_name(target_name).with_known_signature(&signatures);
        if r2types::callee_name_is_import_like(target_name) {
            identity = identity.with_import_linkage_evidence();
        }
        let mut resolution = ctx
            .inputs
            .function_facts
            .callee_resolution()
            .cloned()
            .unwrap_or_default();
        resolution.by_key.insert(key.clone(), identity);
        resolution.by_callsite.insert(
            r2types::CallsiteKey {
                block_addr: source_call.0,
                op_index: source_call.1,
            },
            key,
        );
        mutate_function_facts(ctx, |function_facts| {
            function_facts.set_callee_resolution(resolution);
        });
    }

    fn install_known_one_arg_signature(ctx: &mut FoldingContext<'_>) {
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.one_arg".to_string(),
            FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            },
        )]));
    }

    fn stack_load_call_arg(offset: i64, size: u32) -> crate::analysis::CallArgBinding {
        let value = crate::analysis::SemanticValue::Load {
            space: r2il::SpaceId::Ram,
            addr: crate::analysis::NormalizedAddr {
                base: crate::analysis::BaseRef::StackSlot(offset),
                index: None,
                scale_bytes: 0,
                offset_bytes: 0,
            },
            size,
        };
        let mut binding = crate::analysis::CallArgBinding::input(
            crate::analysis::SemanticCallArg::semantic(value),
        );
        binding.source_var_name = Some(fixture_source_name_for_expr(&binding.arg));
        binding
    }

    fn string_addr_call_arg(addr: u64) -> crate::analysis::CallArgBinding {
        let mut binding = crate::analysis::CallArgBinding::input(
            crate::analysis::SemanticCallArg::StringAddr(addr),
        );
        binding.source_var_name = Some(fixture_source_name_for_expr(&binding.arg));
        binding
    }

    fn install_call_owner(
        ctx: &mut FoldingContext<'_>,
        source_call: (u64, usize),
        owner_name: &str,
        alias: &str,
    ) {
        let source_id = CallSiteId::from(source_call);
        ctx.state.analysis_ctx.ownership.call_ownership.insert(
            source_id,
            CallOwnershipFact {
                source: source_id,
                owner: Some(CallOwner {
                    visible_name: owner_name.to_string(),
                    kind: CallOwnerKind::StableLocal,
                }),
                aliases: BTreeSet::from([alias.to_string()]),
                direct_aliases: BTreeSet::from([alias.to_string()]),
            },
        );
        ctx.state
            .analysis_ctx
            .ownership
            .alias_sources
            .insert(alias.to_string(), source_id);
        ctx.state
            .analysis_ctx
            .ownership
            .alias_sources
            .insert(alias.to_ascii_lowercase(), source_id);
        ctx.state
            .analysis_ctx
            .ownership
            .visible_owner_sources
            .insert(owner_name.to_string(), source_id);
        ctx.state
            .analysis_ctx
            .ownership
            .visible_owner_sources
            .insert(owner_name.to_ascii_lowercase(), source_id);
        ctx.state
            .analysis_ctx
            .ownership
            .visible_owned_names
            .insert(owner_name.to_ascii_lowercase());
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert(alias.to_string(), source_call);
    }

    fn prepared_zero_arg_helper_call(name: &str) -> SourceOwnedPreparedFixture {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });
        prepared_from_r2il_blocks(&[entry], &arch).with_name(name)
    }

    fn prepared_zero_arg_helper_call_with_stack_slot(
        name: &str,
        base: r2ssa::StackAddressBase,
        offset: i64,
    ) -> SourceOwnedPreparedFixture {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });
        let base_offset = match base {
            r2ssa::StackAddressBase::FramePointer => 0x20,
            r2ssa::StackAddressBase::StackPointer => 0x28,
        };
        entry.push(R2ILOp::IntSub {
            dst: Varnode::unique(0x500, 8),
            a: Varnode::register(base_offset, 8),
            b: Varnode::constant(offset.unsigned_abs(), 8),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x500, 8),
            val: Varnode::constant(0, 8),
        });
        prepared_x86_with_stack_slot(&[entry], &arch, base, offset, 8).with_name(name)
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

    fn minimal_callee_fact(addr: u64, name: &str) -> CalleeFact {
        minimal_callee_fact_with_linkage(addr, name, r2types::CalleeLinkage::Unknown)
    }

    fn minimal_callee_fact_with_linkage(
        addr: u64,
        name: &str,
        linkage: r2types::CalleeLinkage,
    ) -> CalleeFact {
        CalleeFact {
            function_id: addr,
            name: Some(name.to_string()),
            linkage,
            signature: None,
            signature_callconv: None,
            signature_noreturn: false,
            model_policy_evidence: BTreeSet::new(),
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

    fn minimal_import_callee_fact(addr: u64, name: &str) -> CalleeFact {
        minimal_callee_fact_with_linkage(addr, name, r2types::CalleeLinkage::Imported)
    }

    fn minimal_modeled_callee_fact(addr: u64, name: &str) -> CalleeFact {
        let mut fact = minimal_callee_fact(addr, name);
        fact.model_policy_evidence
            .insert(r2types::CalleeModelPolicyEvidence::InterprocSummary);
        fact
    }

    fn install_minimal_import_callee_facts(ctx: &mut FoldingContext<'_>, facts: &[(u64, &str)]) {
        install_function_callee_facts(
            ctx,
            facts
                .iter()
                .map(|(addr, name)| (*addr, minimal_import_callee_fact(*addr, name)))
                .collect(),
        );
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
        let empty_ty = Box::leak(Box::new(HashMap::new()));
        FoldingContext::from_inputs(FoldInputs {
            display_names: crate::empty_display_names(),
            arch,
            function_names: empty_u64,
            strings: empty_u64,
            binary_symbols: empty_u64,
            symbols: &test_table(),
            function_facts: empty_function_facts(),
            certified_rendering_required: false,
            stack_slots: empty_stack_slots,
            field_access_certificates: &[],
            external_stack_vars: empty_stack,
            visible_bindings: empty_visible,
            external_type_db: Box::leak(Box::new(r2types::ExternalTypeDb::default())),
            param_register_aliases: empty_str,
            type_hints: empty_ty,
            type_oracle: None,
            function_return_type: None,
            prepared_ssa: None,
            prepared_semantic_view: None,
            prepared_objects: None,
            prepared_memory: None,
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
        let empty_ty = Box::leak(Box::new(HashMap::new()));
        FoldingContext::from_inputs(FoldInputs {
            display_names: crate::empty_display_names(),
            arch,
            function_names: empty_u64,
            strings: empty_u64,
            binary_symbols: empty_u64,
            symbols: &test_table(),
            function_facts: empty_function_facts(),
            certified_rendering_required: false,
            stack_slots: empty_stack_slots,
            field_access_certificates: &[],
            external_stack_vars: empty_stack,
            visible_bindings: empty_visible,
            external_type_db: Box::leak(Box::new(r2types::ExternalTypeDb::default())),
            param_register_aliases: empty_str,
            type_hints: empty_ty,
            type_oracle: None,
            function_return_type: None,
            prepared_ssa: None,
            prepared_semantic_view: None,
            prepared_objects: None,
            prepared_memory: None,
        })
    }

    fn test_callsite_facts(prepared: &r2ssa::SsaArtifact) -> r2types::FunctionCallsiteFacts {
        let by_callsite = prepared
            .certificates()
            .callsites
            .values()
            .filter_map(|cert| {
                let (block_addr, op_index) = prepared.inst_op_site(cert.at)?;
                let callsite = r2types::CallsiteKey {
                    block_addr,
                    op_index,
                };
                let register_argument_locations = cert
                    .argument_certificates
                    .iter()
                    .filter_map(|argument| {
                        let r2ssa::CallArgumentLocation::Register { name } = &argument.location
                        else {
                            return None;
                        };
                        Some(r2types::RegisterCallArgumentLocationFact {
                            index: argument.index,
                            value: argument.value,
                            name: name.clone(),
                            source_inst: argument.source_inst,
                        })
                    })
                    .collect();
                let stack_argument_locations = cert
                    .argument_certificates
                    .iter()
                    .filter_map(|argument| {
                        let r2ssa::CallArgumentLocation::Stack {
                            object,
                            offset,
                            memory_access,
                        } = argument.location
                        else {
                            return None;
                        };
                        Some(r2types::StackCallArgumentLocationFact {
                            index: argument.index,
                            value: argument.value,
                            object,
                            offset,
                            memory_access,
                            source_inst: argument.source_inst,
                        })
                    })
                    .collect();
                Some((
                    callsite,
                    r2types::CallsiteArgumentFacts {
                        callsite,
                        call_site_id: cert.call_site,
                        at: cert.at,
                        target: cert.target,
                        direct_target: cert.direct_target,
                        argument_values: cert
                            .argument_values
                            .iter()
                            .copied()
                            .enumerate()
                            .map(|(index, value)| r2types::CallArgumentValueFact { index, value })
                            .collect(),
                        register_argument_locations,
                        stack_argument_locations,
                    },
                ))
            })
            .collect();
        r2types::FunctionCallsiteFacts { by_callsite }
    }

    fn test_call_result_facts(prepared: &r2ssa::SsaArtifact) -> r2types::FunctionCallResultFacts {
        let mut by_value = BTreeMap::new();
        let mut by_callsite = BTreeMap::<r2types::CallsiteKey, Vec<r2ssa::ValueId>>::new();
        for cert in prepared.certificates().call_results.values() {
            let Some(callsite_cert) = prepared.certificates().callsites.get(&cert.call_site) else {
                continue;
            };
            let callsite = r2types::CallsiteKey {
                block_addr: callsite_cert.block_addr,
                op_index: callsite_cert.op_index,
            };
            by_callsite.entry(callsite).or_default().push(cert.value);
            by_value.insert(
                cert.value,
                r2types::CallResultFact {
                    callsite,
                    call_site_id: cert.call_site,
                    at: cert.at,
                    value: cert.value,
                    width: cert.width,
                    relation: cert.relation,
                    carrier: cert.carrier.clone(),
                    owner: cert.owner.clone(),
                },
            );
        }
        r2types::FunctionCallResultFacts {
            by_value,
            by_callsite,
        }
    }

    fn test_call_result_facts_with_owner_for_source(
        prepared: &r2ssa::SsaArtifact,
        source_call: (u64, usize),
    ) -> r2types::FunctionCallResultFacts {
        let mut facts = test_call_result_facts(prepared);
        let (&object, slot) = prepared
            .certificates()
            .stack_slots
            .iter()
            .find(|(_, slot)| slot.offset == -8)
            .expect("owner mutation requires an exact source-declared stack slot");
        let callsite = r2types::CallsiteKey {
            block_addr: source_call.0,
            op_index: source_call.1,
        };
        let values = facts
            .by_callsite
            .get(&callsite)
            .cloned()
            .unwrap_or_default();
        for value in values {
            if let Some(fact) = facts.by_value.get_mut(&value) {
                fact.owner = Some(r2ssa::ValueOwner::StackSlot {
                    object,
                    offset: slot.offset,
                });
            }
        }
        facts
    }

    fn install_stack_owner_function_facts<'a>(
        ctx: &mut FoldingContext<'a>,
        prepared: &'a SourceOwnedPreparedFixture,
        call_result_facts: r2types::FunctionCallResultFacts,
        name: &str,
        offset: i64,
    ) {
        ctx.inputs.function_facts = prepared.function_facts();
        let render_facts = test_render_facts(prepared);
        mutate_function_facts(ctx, |function_facts| {
            function_facts.replace_type_facts(r2types::FunctionTypeFacts {
                stack_slots: BTreeMap::from([(
                    StackSlotKey {
                        base: ExternalStackBase::StackPointer,
                        offset,
                    },
                    r2types::ExternalStackSlotSpec {
                        name: name.to_string(),
                        ty: Some(r2types::CTypeLike::Int {
                            bits: 64,
                            signedness: r2types::Signedness::Unsigned,
                        }),
                        role: r2types::ExternalStackSlotRole::Local,
                        ..r2types::ExternalStackSlotSpec::default()
                    },
                )]),
                ..r2types::FunctionTypeFacts::default()
            });
            function_facts.set_call_results(call_result_facts);
        });
        assert_eq!(
            ctx.inputs.function_facts.render_facts(),
            &render_facts,
            "stack-owner rendering must come from the exact source-owned report"
        );
    }

    fn test_render_facts(prepared: &SourceOwnedPreparedFixture) -> r2types::FunctionRenderFacts {
        prepared.function_facts().render_facts().clone()
    }

    fn install_function_facts(ctx: &mut FoldingContext<'_>, facts: r2types::FunctionFacts) {
        ctx.inputs.function_facts = Box::leak(Box::new(facts));
    }

    fn mutate_function_facts(
        ctx: &mut FoldingContext<'_>,
        update: impl FnOnce(&mut r2types::FunctionFacts),
    ) {
        let mut facts = ctx.inputs.function_facts.clone();
        update(&mut facts);
        install_function_facts(ctx, facts);
    }

    fn install_function_callee_facts(
        ctx: &mut FoldingContext<'_>,
        facts: BTreeMap<u64, r2types::CalleeFact>,
    ) {
        mutate_function_facts(ctx, |function_facts| {
            let mut type_facts = function_facts.type_facts().clone();
            type_facts.callee_facts = facts;
            function_facts.replace_type_facts(type_facts);
        });
    }

    fn install_function_callsite_facts(
        ctx: &mut FoldingContext<'_>,
        facts: r2types::FunctionCallsiteFacts,
    ) {
        mutate_function_facts(ctx, |function_facts| function_facts.set_callsites(facts));
    }

    fn remove_function_callsite_facts(ctx: &mut FoldingContext<'_>) {
        install_function_callsite_facts(ctx, r2types::FunctionCallsiteFacts::default());
    }

    fn install_function_call_result_facts(
        ctx: &mut FoldingContext<'_>,
        facts: r2types::FunctionCallResultFacts,
    ) {
        mutate_function_facts(ctx, |function_facts| function_facts.set_call_results(facts));
    }


    fn install_function_call_render_facts(
        ctx: &mut FoldingContext<'_>,
        facts: r2types::FunctionCallRenderFacts,
    ) {
        mutate_function_facts(ctx, |function_facts| function_facts.set_call_render(facts));
    }


    fn install_function_control_facts(
        ctx: &mut FoldingContext<'_>,
        facts: r2types::FunctionControlFacts,
    ) {
        mutate_function_facts(ctx, |function_facts| function_facts.set_control(facts));
    }

    fn remove_function_render_facts(ctx: &mut FoldingContext<'_>) {
        let mut facts = r2types::FunctionFacts::new(
            ctx.inputs.function_facts.type_facts().clone(),
            ctx.inputs.function_facts.semantic_artifact().cloned(),
        );
        facts = facts.with_assumptions(ctx.inputs.function_facts.assumptions().clone());
        if let Some(callsites) = ctx.inputs.function_facts.callsites().cloned() {
            facts.set_callsites(callsites);
        }
        if let Some(call_results) = ctx.inputs.function_facts.call_results().cloned() {
            facts.set_call_results(call_results);
        }
        if let Some(call_render) = ctx.inputs.function_facts.call_render().cloned() {
            facts.set_call_render(call_render);
        }
        if let Some(control) = ctx.inputs.function_facts.control().cloned() {
            facts.set_control(control);
        }
        if let Some(route) = ctx.inputs.function_facts.decompile_route().cloned() {
            facts = facts.with_decompile_route(route);
        }
        install_function_facts(ctx, facts);
    }

    fn standard_route_for_test(reason: &str) -> r2types::DecompileRouteFacts {
        r2types::DecompileRouteFacts {
            kind: r2types::DecompileRouteKind::Standard,
            reason: Some(reason.to_string()),
            fallback_comment: None,
            skip_runtime_type_inference: true,
            use_prepared_semantic_view: true,
        }
    }

    fn install_certified_function_facts(ctx: &mut FoldingContext<'_>) {
        let facts = ctx
            .inputs
            .function_facts
            .clone()
            .with_decompile_route(standard_route_for_test("test typed render facts"));
        install_function_facts(ctx, facts);
        ctx.inputs.certified_rendering_required = true;
    }

    fn install_test_x86_64_signature(ctx: &mut FoldingContext<'_>) {
        let signature = r2types::FunctionSignatureSpec {
            ret_type: Some(r2types::CTypeLike::Int {
                bits: 64,
                signedness: r2types::Signedness::Signed,
            }),
            params: vec![r2types::FunctionParamSpec {
                name: "arg1".to_string(),
                ty: Some(r2types::CTypeLike::Int {
                    bits: 64,
                    signedness: r2types::Signedness::Signed,
                }),
            }],
        };
        let certificate = r2types::SignatureCertificate::from_signature(
            &signature,
            [r2types::SignatureCertificateSource::LocalInference],
        )
        .expect("typed test signature");
        mutate_function_facts(ctx, |function_facts| {
            let mut types = function_facts.type_facts().clone();
            types.merged_signature = Some(signature);
            types.signature_certificate = Some(certificate);
            function_facts.replace_type_facts(types);
        });
    }

    fn test_call_render_facts(prepared: &r2ssa::SsaArtifact) -> r2types::FunctionCallRenderFacts {
        let call_results = test_call_result_facts(prepared);
        let by_callsite = prepared
            .certificates()
            .callsites
            .values()
            .map(|cert| {
                let callsite = r2types::CallsiteKey {
                    block_addr: cert.block_addr,
                    op_index: cert.op_index,
                };
                let disposition = if call_results
                    .results_for_site(callsite)
                    .any(|result| matches!(result.owner, Some(r2ssa::ValueOwner::StackSlot { .. })))
                {
                    r2types::CallsiteRenderDisposition::AssignedResult
                } else {
                    r2types::CallsiteRenderDisposition::SideEffectStatement
                };
                (
                    callsite,
                    r2types::CallsiteRenderFact {
                        callsite,
                        target: Some(cert.target),
                        disposition,
                        proof_values: cert.argument_values.clone(),
                        residual_reason: None,
                    },
                )
            })
            .collect();
        r2types::FunctionCallRenderFacts { by_callsite }
    }

    fn make_x86_64_ctx_with_prepared<'a>(
        prepared_ssa: &'a SourceOwnedPreparedFixture,
    ) -> FoldingContext<'a> {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_ssa = Some(prepared_ssa);
        ctx.inputs.function_facts = prepared_ssa.function_facts();
        ctx
    }

    fn make_aarch64_ctx_with_prepared<'a>(
        prepared_ssa: &'a SourceOwnedPreparedFixture,
    ) -> FoldingContext<'a> {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.prepared_ssa = Some(prepared_ssa);
        ctx.inputs.function_facts = prepared_ssa.function_facts();
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
        install_minimal_import_callee_facts(
            ctx,
            &[
                (0x10000259c, "sym.imp.printf"),
                (0x1000025d8, "sym.imp.atoi"),
            ],
        );
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
        ctx.state.analysis_ctx.stack_info.stack_vars =
            HashMap::from([(-8, "buf".to_string()), (-16, "len".to_string())]);

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
        ctx.state.analysis_ctx.stack_info.stack_vars =
            HashMap::from([(-8, "sum".to_string()), (-4, "i".to_string())]);

        let sum_rhs = ctx.collapse_scalar_stack_addr_artifact(CExpr::binary(
            BinaryOp::Add,
            CExpr::AddrOf(Box::new(ctx.name_ref("sum"))),
            CExpr::Subscript {
                base: Box::new(ctx.name_ref("arr")),
                index: Box::new(ctx.name_ref("i")),
            },
        ));
        let i_rhs = ctx.rewrite_scalar_stack_placeholder_rhs(
            &ctx.name_ref("i"),
            ctx.name_ref("local_3"),
        );
        let cross_slot_rhs = ctx.rewrite_scalar_stack_placeholder_rhs(
            &ctx.name_ref("sum"),
            ctx.name_ref("local_17"),
        );

        assert!(
            expr_contains_var(&sum_rhs, "sum") && !expr_contains_addr_of(&sum_rhs),
            "scalar sum update should not expose address aliases: {sum_rhs:?}"
        );
        assert_eq!(
            i_rhs,
            ctx.name_ref("local_3"),
            "adjacent stack placeholders must not become source-shaped scalar arithmetic without value proof"
        );
        assert_eq!(
            cross_slot_rhs,
            ctx.name_ref("local_17"),
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
        ctx.state.analysis_ctx.stack_info.stack_vars = HashMap::from([(-8, "count".to_string())]);

        let offsets = ctx.stack_offsets_for_visible_storage_name({ let CExpr::Var(id) = ctx.name_ref("count") else { unreachable!() }; id });
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
                let lower = ctx.spelling(*name).to_lowercase();
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
            CExpr::External { .. } => false,
            CExpr::Var(name) => &*ctx.spelling(*name) == target,
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
            CExpr::External { .. } => false,
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
    fn callsite_identity_controls_policy_when_rendered_callee_is_poisoned() {
        let symbols = test_table();
        let mut ctx = FoldingContext::new(64);
        let typed_names = HashMap::from([(0x401000, "sym.imp.one_arg".to_string())]);
        let binary_symbols = HashMap::new();
        let callee_facts = BTreeMap::from([(
            0x401000,
            minimal_import_callee_fact(0x401000, "sym.imp.one_arg"),
        )]);
        let known_signatures: HashMap<String, r2types::FunctionType> = HashMap::from([(
            "sym.imp.one_arg".to_string(),
            FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }
            .into(),
        )]);
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
                symbols: &binary_symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_signatures,
            },
        );
        install_function_callee_facts(&mut ctx, callee_facts);
        mutate_function_facts(&mut ctx, |function_facts| {
            function_facts.set_callee_resolution(resolution);
        });

        let poisoned_callee = ctx.name_ref("sym.local_two_arg");
        assert!(
            !ctx.is_imported_call_target(&poisoned_callee),
            "expression-only fallback should not classify the poisoned local name as imported"
        );
        assert!(
            ctx.is_imported_call_target_for_site(0x1000, 0),
            "callsite identity should classify the target from typed resolution"
        );
        assert!(
            !ctx.is_imported_call_target_for_site(0x2000, 0),
            "unresolved callsites must not inherit imported policy from unrelated sites"
        );
        assert_eq!(ctx.non_variadic_call_arity(&poisoned_callee), None);
        assert_eq!(ctx.non_variadic_call_arity_for_site(0x1000, 0), Some(1));
        assert_eq!(
            ctx.normalize_prepared_call_args_for_site(
                0x1000,
                0,
                &poisoned_callee,
                vec![CExpr::IntLit(7), CExpr::IntLit(9)],
            ),
            vec![CExpr::IntLit(7)]
        );
    }

    #[test]
    fn prepared_call_args_do_not_expand_stale_downstream_definitions() {
        let mut ctx = FoldingContext::new(64);
        let rendered_callee = ctx.name_ref("sym.local_helper");

        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("tmp:1_0".to_string(), CExpr::IntLit(42));

        assert_eq!(
            ctx.normalize_call_arg_expr_with_import_policy(
                ctx.name_ref("tmp:1_0"),
                false
            ),
            CExpr::IntLit(42),
            "legacy unprepared call-arg repair still expands low-signal definitions"
        );
        assert_eq!(
            ctx.normalize_prepared_call_args_for_site(
                0x1000,
                0,
                &rendered_callee,
                vec![ctx.name_ref("tmp:1_0")],
            ),
            vec![ctx.name_ref("value_1_0")],
            "prepared arguments are certificate-owned and must not be repaired from local definitions"
        );
    }

    #[test]
    fn callsite_identity_prevents_poisoned_import_name_from_imported_arg_repair() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(&mut ctx, source_call, 0x401000, "sym.local.helper", None);
        let source_id = CallSiteId::from(source_call);
        ctx.state.analysis_ctx.ownership.call_ownership.insert(
            source_id,
            CallOwnershipFact {
                source: source_id,
                owner: Some(CallOwner {
                    visible_name: "owned_result".to_string(),
                    kind: CallOwnerKind::StableLocal,
                }),
                aliases: BTreeSet::from(["tmp_result".to_string()]),
                direct_aliases: BTreeSet::new(),
            },
        );
        ctx.state
            .analysis_ctx
            .ownership
            .alias_sources
            .insert("tmp_result".to_string(), source_id);

        let poisoned_import = ctx.name_ref("sym.imp.printf");
        let real_internal = ctx.name_ref("sym.local.helper");
        let binding = crate::analysis::CallArgBinding::result(
            crate::analysis::SemanticCallArg::FallbackExpr(ctx.name_ref("tmp_result")),
        )
        .with_source_call(source_call.0, source_call.1);
        let expected = ctx.render_call_arg_for_callee(&real_internal, binding.clone());
        assert_ne!(
            expected,
            ctx.name_ref("owned_result"),
            "test setup must distinguish internal rendering from imported result repair"
        );

        assert_eq!(
            ctx.render_call_args_for_site(
                source_call.0,
                source_call.1,
                &poisoned_import,
                vec![binding,]
            ),
            vec![expected],
            "typed internal callsite identity must override a poisoned imported rendered callee for arg policy",
        );
    }

    #[test]
    fn callsite_identity_uses_modeled_policy_for_site_args() {
        let symbols = test_table();
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        let typed_names = HashMap::from([(0x401000, "sym.local.modeled".to_string())]);
        let binary_symbols = HashMap::new();
        let callee_facts = BTreeMap::from([(
            0x401000,
            minimal_modeled_callee_fact(0x401000, "sym.local.modeled"),
        )]);
        let known_signatures = HashMap::new();
        let resolution = r2types::CalleeResolutionFacts::from_direct_call_targets(
            [(
                r2types::CallsiteKey {
                    block_addr: source_call.0,
                    op_index: source_call.1,
                },
                0x401000,
            )],
            &r2types::CalleeIdentityContext {
                function_names: &typed_names,
                symbols: &binary_symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_signatures,
            },
        );
        install_function_callee_facts(&mut ctx, callee_facts);
        mutate_function_facts(&mut ctx, |function_facts| {
            function_facts.set_callee_resolution(resolution);
        });
        let source_id = CallSiteId::from(source_call);
        ctx.state.analysis_ctx.ownership.call_ownership.insert(
            source_id,
            CallOwnershipFact {
                source: source_id,
                owner: Some(CallOwner {
                    visible_name: "owned_result".to_string(),
                    kind: CallOwnerKind::StableLocal,
                }),
                aliases: BTreeSet::from(["tmp_result".to_string()]),
                direct_aliases: BTreeSet::new(),
            },
        );
        ctx.state
            .analysis_ctx
            .ownership
            .alias_sources
            .insert("tmp_result".to_string(), source_id);

        let binding = crate::analysis::CallArgBinding::result(
            crate::analysis::SemanticCallArg::FallbackExpr(ctx.name_ref("tmp_result")),
        )
        .with_source_call(source_call.0, source_call.1);

        assert_eq!(
            ctx.render_call_args_for_site(
                source_call.0,
                source_call.1,
                &ctx.name_ref("sym.local.modeled"),
                vec![binding],
            ),
            vec![ctx.name_ref("owned_result")],
            "typed modeled callsite identity must use imported/modelled argument policy even without an import name",
        );
    }

    #[test]
    fn final_call_normalization_uses_typed_non_variadic_callsite_arity() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(
            &mut ctx,
            source_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );

        let poisoned = CExpr::call(
            ctx.name_ref("sym.local_two_arg"),
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
        );
        let normalized = ctx.normalize_call_expr_for_source_call(
            source_call,
            poisoned,
            FinalExprNormalizeContext::DefinitionRoot,
        );

        assert_eq!(
            normalized,
            CExpr::call(
                ctx.name_ref("sym.imp.one_arg"),
                vec![CExpr::IntLit(7)]
            ),
            "final normalization must keep source-call identity for typed callee arity",
        );
    }

    #[test]
    fn final_call_normalization_requires_typed_callsite_resolution_for_target_repair() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Call {
            target: Varnode::constant(0x401050, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("prepared_direct_call_normalization");
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_ssa = Some(&prepared);

        assert!(
            ctx.inputs.callee_resolution().is_none(),
            "test must prove the prepared direct target fallback, not typed resolution"
        );

        let normalized = ctx.normalize_call_expr_for_source_call(
            (0x1000, 0),
            CExpr::call(
                ctx.name_ref("sym.poisoned"),
                vec![CExpr::IntLit(7)],
            ),
            FinalExprNormalizeContext::DefinitionRoot,
        );

        assert_eq!(
            normalized,
            CExpr::call(
                ctx.name_ref("sym.poisoned"),
                vec![CExpr::IntLit(7)]
            ),
            "prepared direct targets must not repair rendered call targets without typed callsite resolution"
        );
    }

    #[test]
    fn final_call_normalization_uses_typed_callsite_resolution_for_target_repair() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Call {
            target: Varnode::constant(0x401050, 8),
        });
        let prepared =
            prepared_from_r2il_blocks(&[entry], &arch).with_name("typed_direct_call_normalization");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_callsite_resolution(&mut ctx, (0x1000, 0), 0x401050, "sym.helper", None);

        let normalized = ctx.normalize_call_expr_for_source_call(
            (0x1000, 0),
            CExpr::call(
                ctx.name_ref("sym.poisoned"),
                vec![CExpr::IntLit(7)],
            ),
            FinalExprNormalizeContext::DefinitionRoot,
        );

        assert_eq!(
            normalized,
            CExpr::call(ctx.name_ref("sym.helper"), vec![CExpr::IntLit(7)]),
            "typed callsite resolution must outrank rendered callee text"
        );
    }

    #[test]
    fn final_call_normalization_does_not_apply_import_policy_from_poisoned_rendered_name() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(&mut ctx, source_call, 0x401000, "sym.local.helper", None);
        let owner_source = (0x2000, 0);
        let owner_id = CallSiteId::from(owner_source);
        ctx.state.analysis_ctx.ownership.call_ownership.insert(
            owner_id,
            CallOwnershipFact {
                source: owner_id,
                owner: Some(CallOwner {
                    visible_name: "owned_result".to_string(),
                    kind: CallOwnerKind::StableLocal,
                }),
                aliases: BTreeSet::from(["tmp_result".to_string()]),
                direct_aliases: BTreeSet::new(),
            },
        );
        ctx.state
            .analysis_ctx
            .ownership
            .alias_sources
            .insert("tmp_result".to_string(), owner_id);

        let poisoned = CExpr::call(
            ctx.name_ref("sym.imp.printf"),
            vec![ctx.name_ref("tmp_result")],
        );
        let normalized = ctx.normalize_call_expr_for_source_call(
            source_call,
            poisoned,
            FinalExprNormalizeContext::DefinitionRoot,
        );

        assert_eq!(
            normalized,
            CExpr::call(
                ctx.name_ref("sym.local.helper"),
                vec![ctx.name_ref("tmp_result")],
            ),
            "poisoned rendered import names must not trigger imported-arg repair for typed internal callsites",
        );
    }

    #[test]
    fn optional_site_import_policy_prefers_typed_internal_identity_over_rendered_import() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(&mut ctx, source_call, 0x401000, "sym.local.helper", None);

        assert!(
            !ctx.imported_or_modeled_call_target_for_optional_site(Some(source_call)),
            "typed internal callsite identity must not inherit imported policy from the rendered callee",
        );
    }

    #[test]
    fn unresolved_source_call_does_not_authorize_raw_rendered_target_policy() {
        let mut ctx = FoldingContext::new(64);
        install_function_callee_facts(
            &mut ctx,
            BTreeMap::from([(
                0x401000,
                minimal_import_callee_fact(0x401000, "sym.imp.one_arg"),
            )]),
        );
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.one_arg".to_string(),
            FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            },
        )]));

        let raw_rendered_target = ctx.name_ref("const:401000");
        assert!(
            ctx.is_imported_call_target(&raw_rendered_target),
            "source-less direct target queries may still use typed direct-address context"
        );
        assert_eq!(ctx.non_variadic_call_arity(&raw_rendered_target), Some(1));

        assert!(
            !ctx.is_imported_call_target_for_site(0x2000, 0),
            "real callsites without a typed callsite binding must not inherit policy from a rendered direct target"
        );
        assert_eq!(
            ctx.non_variadic_call_arity_for_site(0x2000, 0),
            None,
            "arity truncation also requires a typed source-call identity"
        );
        assert_eq!(
            ctx.render_call_args_for_site(
                0x2000,
                0,
                &raw_rendered_target,
                vec![call_arg(CExpr::IntLit(7)), call_arg(CExpr::IntLit(9))],
            ),
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
            "unresolved source calls must keep standard argument rendering"
        );
    }

    #[test]
    fn unresolved_source_call_does_not_authorize_rendered_import_name_policy_or_signature() {
        let mut ctx = FoldingContext::new(64);
        install_function_callee_facts(
            &mut ctx,
            BTreeMap::from([(
                0x401000,
                minimal_import_callee_fact(0x401000, "sym.imp.one_arg"),
            )]),
        );
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.one_arg".to_string(),
            FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            },
        )]));

        let rendered_import = ctx.name_ref("sym.imp.one_arg");
        let rendered_call = CExpr::call(
            rendered_import.clone(),
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
        );

        assert!(
            !ctx.is_imported_call_target_for_site(0x2000, 0),
            "unresolved source calls must not classify import policy from rendered names"
        );
        assert_eq!(
            ctx.non_variadic_call_arity_for_site(0x2000, 0),
            None,
            "rendered signature names must not truncate unresolved source-call args"
        );
        assert_eq!(
            ctx.expr_type_hint_for_source_call((0x2000, 0), &rendered_call),
            None,
            "rendered signature names must not provide source-call return types"
        );
        assert!(
            !ctx.source_call_expr_returns_void((0x2000, 0), &rendered_call),
            "rendered void signatures must not prune unresolved source-call results"
        );
        assert_eq!(
            ctx.render_call_args_for_site(
                0x2000,
                0,
                &rendered_import,
                vec![call_arg(CExpr::IntLit(7)), call_arg(CExpr::IntLit(9))],
            ),
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
            "unresolved source calls must keep standard argument rendering"
        );
    }

    #[test]
    fn prepared_call_identity_authorizes_policy_without_rendered_callee_trust() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Call {
            target: Varnode::constant(0x401000, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("prepared_policy")
            .with_context(r2types::ParsedExternalContext {
                callee_facts: BTreeMap::from([(
                    0x401000,
                    minimal_import_callee_fact(0x401000, "sym.imp.one_arg"),
                )]),
                known_function_signatures: HashMap::from([(
                    "sym.imp.one_arg".to_string(),
                    FunctionType {
                        return_type: CType::Void,
                        params: vec![CType::Int(32)],
                        variadic: false,
                    }
                    .into(),
                )]),
                ..r2types::ParsedExternalContext::default()
            });
        let ctx = make_x86_64_ctx_with_prepared(&prepared);

        let poisoned_rendered_callee = ctx.name_ref("sym.local_poison");
        assert!(
            ctx.is_imported_call_target_for_site(0x1000, 0),
            "prepared call identity should authorize imported policy without trusting rendered callee text"
        );
        assert_eq!(
            ctx.non_variadic_call_arity_for_site(0x1000, 0),
            Some(1),
            "prepared call identity should carry typed signature arity"
        );
        assert_eq!(
            ctx.render_call_args_for_site(
                0x1000,
                0,
                &poisoned_rendered_callee,
                vec![call_arg(CExpr::IntLit(7)), call_arg(CExpr::IntLit(9))],
            ),
            vec![CExpr::IntLit(7)],
            "prepared call identity policy should control imported arg rendering and arity"
        );
    }

    #[test]
    fn final_call_normalization_uses_typed_printf_identity_not_rendered_name() {
        let symbols = test_table();
        let mut imported_ctx = FoldingContext::new(64);
        let imported_source = (0x1000, 0);
        install_callsite_resolution(
            &mut imported_ctx,
            imported_source,
            0x401000,
            "sym.imp.printf",
            Some(FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            }),
        );
        let rendered_local_logger = CExpr::call(
            crate::symbol::var_ref(&symbols, "sym.local_logger"),
            vec![
                CExpr::StringLit("x=%d".to_string()),
                crate::symbol::var_ref(&symbols, "x"),
                crate::symbol::var_ref(&symbols, "garbage"),
            ],
        );

        assert_eq!(
            imported_ctx.normalize_call_expr_for_source_call(
                imported_source,
                rendered_local_logger,
                FinalExprNormalizeContext::DefinitionRoot,
            ),
            CExpr::call(
                crate::symbol::var_ref(&symbols, "sym.imp.printf"),
                vec![
                    CExpr::StringLit("x=%d".to_string()),
                    crate::symbol::var_ref(&symbols, "x"),
                    crate::symbol::var_ref(&symbols, "garbage"),
                ],
            ),
            "typed variadic printf callsite identity must preserve certified args; format strings are not arity proof",
        );

        let mut internal_ctx = FoldingContext::new(64);
        let internal_source = (0x1000, 1);
        install_callsite_resolution(
            &mut internal_ctx,
            internal_source,
            0x402000,
            "sym.local_logger",
            Some(FunctionType {
                return_type: CType::Int(32),
                params: Vec::new(),
                variadic: true,
            }),
        );
        let poisoned_printf = CExpr::call(
            crate::symbol::var_ref(&symbols, "sym.imp.printf"),
            vec![
                CExpr::StringLit("x=%d".to_string()),
                crate::symbol::var_ref(&symbols, "x"),
                crate::symbol::var_ref(&symbols, "garbage"),
            ],
        );

        assert_eq!(
            internal_ctx.normalize_call_expr_for_source_call(
                internal_source,
                poisoned_printf,
                FinalExprNormalizeContext::DefinitionRoot,
            ),
            CExpr::call(
                crate::symbol::var_ref(&symbols, "sym.local_logger"),
                vec![
                    CExpr::StringLit("x=%d".to_string()),
                    crate::symbol::var_ref(&symbols, "x"),
                    crate::symbol::var_ref(&symbols, "garbage"),
                ],
            ),
            "rendered printf names must not clamp args for typed internal callsites",
        );
    }

    #[test]
    fn source_call_identity_residualizes_replayed_imported_result_call_arg() {
        let symbols = test_table();
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(
            &mut ctx,
            source_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );

        let poisoned_func = ctx.name_ref("sym.local_two_arg");
        let binding = crate::analysis::CallArgBinding::result(
            crate::analysis::SemanticCallArg::FallbackExpr(CExpr::call(
                poisoned_func.clone(),
                vec![CExpr::IntLit(7), CExpr::IntLit(9)],
            )),
        )
        .with_source_call(source_call.0, source_call.1);

        assert_eq!(
            ctx.render_call_args_for_site(
                source_call.0,
                source_call.1,
                &poisoned_func,
                vec![binding],
            ),
            vec![ctx.unresolved_call_arg_expr()],
            "source-call replay must not render an uncertified nested call argument",
        );
    }

    #[test]
    fn source_call_identity_residualizes_replayed_result_call_with_transient_arg() {
        let symbols = test_table();
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(
            &mut ctx,
            source_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert(source_call, vec![call_arg(CExpr::IntLit(7))]);

        let poisoned_func = ctx.name_ref("sym.local_two_arg");
        let binding = crate::analysis::CallArgBinding::result(
            crate::analysis::SemanticCallArg::FallbackExpr(CExpr::call(
                poisoned_func.clone(),
                vec![CExpr::call(
                    ctx.name_ref("sym.local_nested"),
                    vec![],
                )],
            )),
        )
        .with_source_call(source_call.0, source_call.1);

        assert_eq!(
            ctx.render_call_args_for_site(
                source_call.0,
                source_call.1,
                &poisoned_func,
                vec![binding],
            ),
            vec![ctx.unresolved_call_arg_expr()],
            "transient replayed args must refuse uncertified nested call arguments",
        );
    }

    #[test]
    fn source_call_identity_refuses_uncertified_nested_call_arg_with_typed_policy() {
        let symbols = test_table();
        let mut ctx = FoldingContext::new(64);
        let outer_call = (0x1000, 0);
        let nested_call_site = (0x2000, 0);
        install_callsite_resolution(
            &mut ctx,
            outer_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        install_indirect_callsite_identity(
            &mut ctx,
            nested_call_site,
            "sym.imp.nested_one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert(outer_call, vec![call_arg(CExpr::IntLit(99))]);

        let nested = CExpr::call(
            ctx.name_ref("sym.imp.nested_one_arg"),
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(nested_call_site, nested.clone());

        assert!(
            !ctx.is_imported_call_target(&ctx.name_ref("sym.imp.nested_one_arg")),
            "test setup requires rendered nested callee text to be insufficient by itself"
        );

        let poisoned_outer_func = ctx.name_ref("sym.local_outer");
        let binding = crate::analysis::CallArgBinding::result(
            crate::analysis::SemanticCallArg::FallbackExpr(CExpr::call(
                poisoned_outer_func.clone(),
                vec![nested.clone()],
            )),
        )
        .with_source_call(outer_call.0, outer_call.1);

        assert_eq!(
            ctx.render_call_args_for_site(
                outer_call.0,
                outer_call.1,
                &poisoned_outer_func,
                vec![binding],
            ),
            vec![ctx.unresolved_call_arg_expr()],
            "source-proven text without certified call-argument proof must not render as executable nested C",
        );
    }

    #[test]
    fn source_call_identity_residualizes_when_nested_rendered_import_contradicts_typed_source() {
        let symbols = test_table();
        let mut ctx = FoldingContext::new(64);
        let outer_call = (0x1000, 0);
        let nested_call_site = (0x2000, 0);
        install_callsite_resolution(
            &mut ctx,
            outer_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        install_minimal_import_callee_facts(&mut ctx, &[(0x402000, "sym.imp.nested_one_arg")]);
        install_indirect_callsite_identity(
            &mut ctx,
            nested_call_site,
            "sym.local.internal_nested",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert(outer_call, vec![call_arg(CExpr::IntLit(99))]);

        let nested = CExpr::call(
            ctx.name_ref("sym.imp.nested_one_arg"),
            vec![CExpr::IntLit(7)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(nested_call_site, nested.clone());

        assert!(
            !ctx.is_imported_call_target(&ctx.name_ref("sym.imp.nested_one_arg")),
            "rendered callee text is display-only and must not authorize import policy"
        );

        let poisoned_outer_func = ctx.name_ref("sym.local_outer");
        let binding = crate::analysis::CallArgBinding::result(
            crate::analysis::SemanticCallArg::FallbackExpr(CExpr::call(
                poisoned_outer_func.clone(),
                vec![nested],
            )),
        )
        .with_source_call(outer_call.0, outer_call.1);

        assert_eq!(
            ctx.render_call_args_for_site(
                outer_call.0,
                outer_call.1,
                &poisoned_outer_func,
                vec![binding],
            ),
            vec![ctx.unresolved_call_arg_expr()],
            "typed/rendered disagreement for a nested source call must refuse executable call-arg C",
        );
    }

    #[test]
    fn source_call_identity_residualizes_when_nested_source_match_is_ambiguous() {
        let symbols = test_table();
        let mut ctx = FoldingContext::new(64);
        let outer_call = (0x1000, 0);
        let first_nested_call_site = (0x2000, 0);
        let second_nested_call_site = (0x3000, 0);
        install_callsite_resolution(
            &mut ctx,
            outer_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        install_minimal_import_callee_facts(&mut ctx, &[(0x402000, "sym.imp.nested_one_arg")]);
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert(outer_call, vec![call_arg(CExpr::IntLit(99))]);

        let nested = CExpr::call(
            ctx.name_ref("sym.imp.nested_one_arg"),
            vec![CExpr::IntLit(7)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(first_nested_call_site, nested.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(second_nested_call_site, nested.clone());

        let poisoned_outer_func = ctx.name_ref("sym.local_outer");
        let binding = crate::analysis::CallArgBinding::result(
            crate::analysis::SemanticCallArg::FallbackExpr(CExpr::call(
                poisoned_outer_func.clone(),
                vec![nested],
            )),
        )
        .with_source_call(outer_call.0, outer_call.1);

        assert_eq!(
            ctx.render_call_args_for_site(
                outer_call.0,
                outer_call.1,
                &poisoned_outer_func,
                vec![binding],
            ),
            vec![ctx.unresolved_call_arg_expr()],
            "ambiguous nested source-call matches must refuse instead of picking a source",
        );
    }

    #[test]
    fn source_keyed_normalization_uses_typed_identity_for_poisoned_cached_call() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(
            &mut ctx,
            source_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        ctx.state.analysis_ctx.use_info.call_result_exprs.insert(
            source_call,
            CExpr::call(
                ctx.name_ref("sym.local_two_arg"),
                vec![CExpr::IntLit(7)],
            ),
        );

        let poisoned = CExpr::call(
            ctx.name_ref("sym.local_two_arg"),
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
        );
        assert_eq!(
            ctx.normalize_call_expr_for_source_call(
                source_call,
                poisoned.clone(),
                FinalExprNormalizeContext::DefinitionRoot,
            ),
            CExpr::call(
                ctx.name_ref("sym.imp.one_arg"),
                vec![CExpr::IntLit(7)],
            ),
            "source-keyed normalization must render the typed callsite callee and arity",
        );
        assert_eq!(
            ctx.normalize_final_call_expr_in_context(
                poisoned.clone(),
                FinalExprNormalizeContext::DefinitionRoot,
            ),
            poisoned,
            "plain final normalization must not infer source provenance from rendered calls",
        );
    }

    #[test]
    fn source_less_final_normalization_keeps_poisoned_cached_call_args() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(
            &mut ctx,
            source_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        ctx.state.analysis_ctx.use_info.call_result_exprs.insert(
            source_call,
            CExpr::call(
                ctx.name_ref("sym.local_two_arg"),
                vec![CExpr::IntLit(7)],
            ),
        );

        let rendered = CExpr::call(
            ctx.name_ref("sym.imp.one_arg"),
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
        );

        assert_eq!(
            ctx.normalize_final_call_expr_in_context(
                rendered.clone(),
                FinalExprNormalizeContext::DefinitionRoot,
            ),
            rendered,
            "typed target identity is insufficient without source-call provenance",
        );
    }

    #[test]
    fn imported_arg_nested_call_without_source_residualizes_instead_of_truncating() {
        let symbols = test_table();
        let mut ctx = FoldingContext::new(64);
        install_known_one_arg_signature(&mut ctx);
        let call = CExpr::call(
            ctx.name_ref("sym.imp.one_arg"),
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
        );

        assert_eq!(
            ctx.normalize_imported_call_arg_expr(call.clone(), false, false, true),
            ctx.unresolved_call_arg_expr(),
            "source-less nested call arguments must refuse instead of being truncated or rendered"
        );
    }

    #[test]
    fn source_call_normalization_canonicalizes_cast_wrapped_call() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(
            &mut ctx,
            source_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        let wrapped = CExpr::cast(
            CType::Int(64),
            CExpr::call(
                ctx.name_ref("sym.local_two_arg"),
                vec![CExpr::IntLit(7), CExpr::IntLit(9)],
            ),
        );

        assert_eq!(
            ctx.normalize_call_expr_for_source_call(
                source_call,
                wrapped,
                FinalExprNormalizeContext::DefinitionRoot,
            ),
            CExpr::cast(
                CType::Int(64),
                CExpr::call(
                    ctx.name_ref("sym.imp.one_arg"),
                    vec![CExpr::IntLit(7)]
                ),
            ),
            "explicit source-call provenance must survive transparent casts"
        );
    }

    #[test]
    fn source_keyed_materialization_rejects_non_call_cached_candidate() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, ctx.name_ref("not_a_call"));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "X20_1".to_string(),
            CExpr::call(
                ctx.name_ref("sym.imp.one_arg"),
                vec![CExpr::IntLit(7)],
            ),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .use_counts
            .insert("x20_1".to_string(), 1);

        let rendered = CExpr::call(
            ctx.name_ref("sym.imp.one_arg"),
            vec![CExpr::IntLit(7)],
        );
        assert_eq!(
            ctx.materializable_call_result_expr_for_call_expr(source_call, &rendered),
            None
        );
    }

    #[test]
    fn recovered_visible_owner_rhs_canonicalizes_poisoned_cached_source_call() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(
            &mut ctx,
            source_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        let source_id = CallSiteId::from(source_call);
        ctx.state.analysis_ctx.ownership.call_ownership.insert(
            source_id,
            CallOwnershipFact {
                source: source_id,
                owner: Some(CallOwner {
                    visible_name: "owned_result".to_string(),
                    kind: CallOwnerKind::StableLocal,
                }),
                aliases: BTreeSet::new(),
                direct_aliases: BTreeSet::new(),
            },
        );
        ctx.state
            .analysis_ctx
            .ownership
            .visible_owner_sources
            .insert("owned_result".to_string(), source_id);
        ctx.state.analysis_ctx.use_info.call_result_exprs.insert(
            source_call,
            CExpr::call(
                ctx.name_ref("sym.local_two_arg"),
                vec![CExpr::IntLit(7), CExpr::IntLit(9)],
            ),
        );

        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs_for_visible_name({ let CExpr::Var(id) = ctx.name_ref("owned_result") else { unreachable!() }; id }),
            Some(CExpr::call(
                ctx.name_ref("sym.imp.one_arg"),
                vec![CExpr::IntLit(7)]
            )),
            "source-keyed recovered RHS must canonicalize the call target before generic normalization",
        );
    }

    #[test]
    fn certified_visible_owner_rhs_rejects_synthesized_call_without_owner_fact() {
        let prepared = prepared_zero_arg_helper_call("certified_replay_callsite");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_certified_function_facts(&mut ctx);
        let source_call = (0x1000, 1);
        ctx.set_external_stack_vars(HashMap::from([(
            -8,
            stack_var_spec("owned_result", Some(CType::u64()), Some("rbp")),
        )]));
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        install_callsite_resolution(&mut ctx, source_call, 0x401050, "sym.helper", None);
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                source_call,
                crate::analysis::PreparedCallView {
                    result_owner: Some(ctx.name_ref("owned_result")),
                    ..crate::analysis::PreparedCallView::default()
                },
            )]),
            ..PreparedSemanticView::default()
        })));
        ctx.state.analysis_ctx.use_info.call_result_exprs.insert(
            source_call,
            CExpr::call(
                ctx.name_ref("sym.local.poisoned"),
                vec![CExpr::IntLit(7)],
            ),
        );

        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs_for_visible_name({ let CExpr::Var(id) = ctx.name_ref("owned_result") else { unreachable!() }; id }),
            None,
            "certified replay must not synthesize a visible owner call without FunctionFacts owner proof"
        );
    }

    #[test]
    fn recovered_direct_call_rhs_rejects_rendered_key_without_source_provenance() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(
            &mut ctx,
            source_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        let poisoned = CExpr::call(
            ctx.name_ref("sym.local_two_arg"),
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
        );

        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs("owned_result", &poisoned),
            None,
            "rendered call RHS recovery must not use expression-key ownership without source provenance",
        );
        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs("wrong_owner", &poisoned),
            None,
            "direct call RHS recovery must still require the recovered owner to match the assignment lhs",
        );
        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs(
                "owned_result",
                &CExpr::Paren(Box::new(poisoned)),
            ),
            None,
            "paren/cast wrappers must not recover owners without source provenance",
        );
    }

    #[test]
    fn recovered_direct_call_rhs_accepts_exact_source_call_and_checks_owner() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(
            &mut ctx,
            source_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        let source_id = CallSiteId::from(source_call);
        ctx.state.analysis_ctx.ownership.call_ownership.insert(
            source_id,
            CallOwnershipFact {
                source: source_id,
                owner: Some(CallOwner {
                    visible_name: "owned_result".to_string(),
                    kind: CallOwnerKind::StableLocal,
                }),
                aliases: BTreeSet::new(),
                direct_aliases: BTreeSet::new(),
            },
        );
        let source_expr = CExpr::call(
            ctx.name_ref("sym.local_two_arg"),
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, source_expr.clone());

        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs("owned_result", &source_expr),
            Some(CExpr::call(
                ctx.name_ref("sym.imp.one_arg"),
                vec![CExpr::IntLit(7)]
            )),
            "exact source-call RHS recovery must canonicalize through typed callsite identity",
        );
        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs("wrong_owner", &source_expr),
            None,
            "exact source-call RHS recovery must reject mismatched owners",
        );
        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs(
                "owned_result",
                &CExpr::Paren(Box::new(source_expr)),
            ),
            Some(CExpr::call(
                ctx.name_ref("sym.imp.one_arg"),
                vec![CExpr::IntLit(7)]
            )),
            "paren/cast wrappers must recurse into exact source-call RHS recovery",
        );
    }

    #[test]
    fn recovered_var_rhs_canonicalizes_alias_source_call_and_checks_owner() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_callsite_resolution(
            &mut ctx,
            source_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        let source_id = CallSiteId::from(source_call);
        ctx.state.analysis_ctx.ownership.call_ownership.insert(
            source_id,
            CallOwnershipFact {
                source: source_id,
                owner: Some(CallOwner {
                    visible_name: "owned_result".to_string(),
                    kind: CallOwnerKind::StableLocal,
                }),
                aliases: BTreeSet::from(["tmp_result".to_string()]),
                direct_aliases: BTreeSet::new(),
            },
        );
        ctx.state
            .analysis_ctx
            .ownership
            .alias_sources
            .insert("tmp_result".to_string(), source_id);
        ctx.state.analysis_ctx.use_info.call_result_exprs.insert(
            source_call,
            CExpr::call(
                ctx.name_ref("sym.local_two_arg"),
                vec![CExpr::IntLit(7), CExpr::IntLit(9)],
            ),
        );

        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs(
                "owned_result",
                &ctx.name_ref("tmp_result"),
            ),
            Some(CExpr::call(
                ctx.name_ref("sym.imp.one_arg"),
                vec![CExpr::IntLit(7)]
            )),
            "alias-source RHS recovery must canonicalize through typed callsite identity",
        );
        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs(
                "wrong_owner",
                &ctx.name_ref("tmp_result"),
            ),
            None,
            "alias-source RHS recovery must reject mismatched assignment owners",
        );
    }

    #[test]
    fn callsite_identity_does_not_printf_clamp_when_rendered_callee_is_poisoned() {
        let symbols = test_table();
        let mut ctx = FoldingContext::new(64);
        let typed_names = HashMap::from([(0x401000, "sym.imp.printf".to_string())]);
        let binary_symbols = HashMap::new();
        let callee_facts = BTreeMap::from([(
            0x401000,
            minimal_import_callee_fact(0x401000, "sym.imp.printf"),
        )]);
        let known_signatures: HashMap<String, r2types::FunctionType> = HashMap::from([(
            "sym.imp.printf".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            }
            .into(),
        )]);
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
                symbols: &binary_symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_signatures,
            },
        );
        install_function_callee_facts(&mut ctx, callee_facts);
        mutate_function_facts(&mut ctx, |function_facts| {
            function_facts.set_callee_resolution(resolution);
        });

        let poisoned_callee = ctx.name_ref("sym.local_logger");
        assert_eq!(
            ctx.normalize_prepared_call_args_for_site(
                0x1000,
                0,
                &poisoned_callee,
                vec![
                    CExpr::StringLit("value=%d\n".to_string()),
                    ctx.name_ref("x"),
                    ctx.name_ref("garbage"),
                ],
            ),
            vec![
                CExpr::StringLit("value=%d\n".to_string()),
                ctx.name_ref("x"),
                ctx.name_ref("garbage"),
            ]
        );
    }

    #[test]
    fn modeled_call_target_uses_typed_resolution_without_fact_scan() {
        let symbols = test_table();
        let mut ctx = FoldingContext::new(64);
        let typed_names = HashMap::from([(0x401000, "sym.local.memcpy_model".to_string())]);
        let binary_symbols = HashMap::new();
        let callee_facts = BTreeMap::from([(
            0x401000,
            minimal_modeled_callee_fact(0x401000, "sym.local.memcpy_model"),
        )]);
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
                symbols: &binary_symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_signatures,
            },
        );
        install_function_callee_facts(&mut ctx, callee_facts);
        mutate_function_facts(&mut ctx, |function_facts| {
            function_facts.set_callee_resolution(resolution);
        });

        let poisoned_callee = ctx.name_ref("sym.local_copy");
        assert!(
            !ctx.is_modeled_call_target(&poisoned_callee),
            "expression-only fallback should not classify the poisoned local name as modeled"
        );
        assert!(
            ctx.is_modeled_call_target_for_site(0x1000, 0),
            "callsite identity should classify the modeled target from typed resolution"
        );
        assert!(
            !ctx.is_modeled_call_target_for_site(0x2000, 0),
            "unresolved callsites must not inherit modeled policy from unrelated sites"
        );
    }

    #[test]
    fn fallback_indirect_call_lowering_uses_typed_callsite_identity() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_indirect_callsite_identity(&mut ctx, source_call, "sym.imp.printf", None);
        ctx.current_block_addr.set(Some(source_call.0));
        ctx.current_op_idx.set(Some(source_call.1));

        let stmt = ctx
            .op_to_stmt_impl(&SSAOp::CallInd {
                target: make_var("X16", 0, 8),
            })
            .expect("fallback indirect call statement");

        assert_eq!(
            stmt,
            CStmt::Expr(CExpr::call(
                ctx.name_ref("sym.imp.printf"),
                vec![]
            )),
            "fallback indirect call lowering must use typed callsite identity instead of rendering the target register",
        );
    }

    #[test]
    fn call_with_args_lowering_residualizes_typed_identity_without_callsite_facts() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_indirect_callsite_identity(&mut ctx, source_call, "sym.imp.printf", None);

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("X16", 0, 8),
                },
                source_call.0,
                source_call.1,
            )
            .expect("call-with-args fallback statement");

        assert!(
            matches!(&stmt, CStmt::Comment(comment) if comment.contains("uncertified callsite arguments")),
            "typed callee identity alone must not authorize executable call-with-args output: {stmt:?}",
        );
    }

    #[test]
    fn indirect_call_with_args_lowering_residualizes_typed_identity_without_callsite_facts() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_indirect_callsite_identity(&mut ctx, source_call, "sym.imp.printf", None);

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::CallInd {
                    target: make_var("X16", 0, 8),
                },
                source_call.0,
                source_call.1,
            )
            .expect("indirect call-with-args fallback statement");

        assert!(
            matches!(&stmt, CStmt::Comment(comment) if comment.contains("uncertified indirect-call arguments")),
            "typed callee identity alone must not authorize executable indirect call-with-args output: {stmt:?}",
        );
    }

    #[test]
    fn indirect_call_lowering_residualizes_unproven_site_arguments() {
        let mut ctx = FoldingContext::new(64);
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![crate::analysis::CallArgBinding::input(
                crate::analysis::SemanticCallArg::FallbackExpr(ctx.name_ref("arg0")),
            )],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::CallInd {
                    target: make_var("call_target", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("indirect call should emit residual statement");

        let CStmt::Comment(comment) = stmt else {
            panic!("expected residual comment for unproven indirect call args, got {stmt:?}");
        };
        assert!(
            comment.contains("uncertified indirect-call arguments"),
            "unproven indirect call arguments must not render as executable C: {comment}"
        );
    }

    #[test]
    fn test_imported_printf_result_slot_residualizes_unlock_call_without_certified_source() {
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
        insert_authorized_call_args(
            &mut ctx,
            (0x1000, 0),
            vec![
                stack_load_call_arg(-44, 4),
                stack_load_call_arg(-48, 4),
                stack_load_call_arg(-52, 4),
            ],
        );
        let __fixture_args = (
            (0x1000, 1),
            vec![
                string_addr_call_arg(0x10000266f),
                stack_load_call_arg(-44, 4).with_stack_offset(0),
                stack_load_call_arg(-48, 4).with_stack_offset(8),
                stack_load_call_arg(-52, 4).with_stack_offset(16),
                result_call_arg(
                    CExpr::call(
                        ctx.name_ref("sym._unlock"),
                        vec![
                            ctx.name_ref("argc"),
                            ctx.name_ref("argc"),
                            CExpr::call(
                                ctx.name_ref("sym.imp.atoi"),
                                vec![CExpr::Deref(Box::new(CExpr::binary(
                                    BinaryOp::Add,
                                    ctx.name_ref("argv"),
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
        insert_authorized_call_args(
            &mut ctx,
            __fixture_args.0,
            __fixture_args.1,
        );;

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
                0x1000,
                1,
            )
            .expect("printf call should emit statement");

        let CStmt::Comment(comment) = stmt else {
            panic!("expected residual printf call, got {stmt:?}");
        };
        assert!(
            comment.contains("uncertified callsite arguments"),
            "printf with uncertified helper result must residualize, got {comment}"
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
        let __fixture_args = (
            (0x1000, 0),
            vec![
                call_arg(ctx.name_ref("a")),
                call_arg(ctx.name_ref("b")),
                call_arg(ctx.name_ref("c")),
            ],
        );
        insert_authorized_call_args(
            &mut ctx,
            __fixture_args.0,
            __fixture_args.1,
        );;
        let helper_call = CExpr::call(
            ctx.name_ref("sym._unlock"),
            vec![
                ctx.name_ref("a"),
                ctx.name_ref("b"),
                ctx.name_ref("c"),
            ],
        );
        let __fixture_args = (
            (0x1000, 1),
            vec![
                string_addr_call_arg(0x40229e),
                call_arg(helper_call.clone()),
                call_arg(ctx.name_ref("b")),
                call_arg(ctx.name_ref("c")),
                result_call_arg(helper_call.clone(), (0x1000, 0), 24),
            ],
        );
        insert_authorized_call_args(
            &mut ctx,
            __fixture_args.0,
            __fixture_args.1,
        );;

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401030", 0, 8),
                },
                0x1000,
                1,
            )
            .expect("printf call should emit statement");

        let CStmt::Comment(comment) = stmt else {
            panic!("expected residual printf call, got {stmt:?}");
        };
        assert!(
            comment.contains("uncertified callsite arguments"),
            "uncertified printf sibling/result call arguments must residualize, got {comment}"
        );
    }

    #[test]
    fn test_imported_printf_result_slot_residualizes_solve_equation_call_without_certified_source()
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
        insert_authorized_call_args(&mut ctx, (0x2000, 0), vec![stack_load_call_arg(-92, 4)]);
        let __fixture_args = (
            (0x2000, 1),
            vec![
                string_addr_call_arg(0x1000026c9),
                stack_load_call_arg(-92, 4).with_stack_offset(0),
                result_call_arg(
                    CExpr::call(
                        ctx.name_ref("sym._solve_equation"),
                        vec![ctx.name_ref("argc")],
                    ),
                    (0x2000, 0),
                    8,
                ),
            ],
        );
        insert_authorized_call_args(
            &mut ctx,
            __fixture_args.0,
            __fixture_args.1,
        );;

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
                0x2000,
                1,
            )
            .expect("printf call should emit statement");

        let CStmt::Comment(comment) = stmt else {
            panic!("expected residual printf call, got {stmt:?}");
        };
        assert!(
            comment.contains("uncertified callsite arguments"),
            "solve_equation printf with uncertified helper result must residualize, got {comment}"
        );
    }

    #[test]
    fn test_imported_printf_result_slot_residualizes_complex_check_call_without_certified_source() {
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
        insert_authorized_call_args(
            &mut ctx,
            (0x3000, 0),
            vec![stack_load_call_arg(-96, 4), stack_load_call_arg(-100, 4)],
        );
        let __fixture_args = (
            (0x3000, 1),
            vec![
                string_addr_call_arg(0x100002701),
                stack_load_call_arg(-96, 4).with_stack_offset(0),
                stack_load_call_arg(-100, 4).with_stack_offset(8),
                result_call_arg(
                    CExpr::call(
                        ctx.name_ref("sym._complex_check"),
                        vec![
                            ctx.name_ref("argc"),
                            CExpr::call(
                                ctx.name_ref("sym.imp.atoi"),
                                vec![CExpr::Deref(Box::new(CExpr::binary(
                                    BinaryOp::Add,
                                    ctx.name_ref("argv"),
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
        insert_authorized_call_args(
            &mut ctx,
            __fixture_args.0,
            __fixture_args.1,
        );;

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:10000259c", 0, 8),
                },
                0x3000,
                1,
            )
            .expect("printf call should emit statement");

        let CStmt::Comment(comment) = stmt else {
            panic!("expected residual printf call, got {stmt:?}");
        };
        assert!(
            comment.contains("uncertified callsite arguments"),
            "complex_check printf with uncertified helper result must residualize, got {comment}"
        );
    }

    #[test]
    fn imported_result_binding_residualizes_when_named_owner_is_not_stable() {
        let symbols = test_table();
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
            .insert((0x1000, 0), vec![call_arg(ctx.name_ref("src"))]);

        let rendered = ctx.render_call_arg_for_callee(
            &ctx.name_ref("sym.imp.printf"),
            result_call_arg(
                CExpr::call(
                    ctx.name_ref("sym.imp.malloc"),
                    vec![CExpr::IntLit(16)],
                ),
                (0x1000, 0),
                0,
            ),
        );

        assert_eq!(
            rendered,
            ctx.unresolved_call_arg_expr(),
            "unstable owner candidates must not fall back to replayed malloc call"
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
                ctx.name_ref("sym.imp.malloc"),
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
                space: r2il::SpaceId::Ram,
                addr: len_slot.clone(),
                val: len,
            },
            SSAOp::Load {
                dst: len_load.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: buf_slot.clone(),
                val: buf_store,
            },
            SSAOp::Load {
                dst: buf_load.clone(),
                space: r2il::SpaceId::Ram,
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

        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (block.addr, 6),
                crate::analysis::PreparedCallView {
                    result_owner: Some(ctx.name_ref("buf")),
                    ..crate::analysis::PreparedCallView::default()
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let rhs = ctx.resolve_predicate_rhs_for_var(&cond, ctx.get_expr(&cond));
        assert!(
            matches!(
                rhs,
                CExpr::Binary {
                    op: BinaryOp::Ne,
                    ref left,
                    ref right,
                } if matches!(left.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "buf")
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
                } if matches!(left.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "loc")
                    && matches!(right.as_ref(), CExpr::IntLit(0))
            ),
            "expected direct call-result null-check to use the named owner alias, got {rhs:?}; call_sources={:?}; aliases={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state.analysis_ctx.use_info.call_result_aliases
        );
    }

    #[test]
    fn predicate_owner_rewrite_rejects_generic_argument_owner() {
        let mut ctx = make_x86_64_ctx();
        install_call_owner(&mut ctx, (0x1000, 2), "arg1", "rax_1");

        let predicate = CExpr::binary(
            BinaryOp::Eq,
            ctx.name_ref("rax_1"),
            CExpr::IntLit(0),
        );

        assert_eq!(
            ctx.normalize_assignment_predicate_rhs(predicate.clone()),
            predicate,
            "generic argument-like owner names are not proof of a stable predicate owner"
        );
    }

    #[test]
    fn predicate_owner_rewrite_uses_source_keyed_owner_for_alias_var() {
        let mut ctx = make_x86_64_ctx();
        install_call_owner(&mut ctx, (0x1000, 2), "loc", "rax_1");

        let predicate = CExpr::binary(
            BinaryOp::Eq,
            ctx.name_ref("rax_1"),
            CExpr::IntLit(0),
        );

        assert_eq!(
            ctx.normalize_assignment_predicate_rhs(predicate),
            CExpr::binary(
                BinaryOp::Eq,
                ctx.name_ref("loc"),
                CExpr::IntLit(0)
            ),
            "source-backed aliases should rewrite to the stable predicate owner"
        );
    }

    #[test]
    fn predicate_owner_rewrite_recurses_into_call_args_without_using_call_as_source() {
        let mut ctx = make_x86_64_ctx();
        install_call_owner(&mut ctx, (0x1000, 2), "loc", "rax_1");

        let predicate = CExpr::binary(
            BinaryOp::Eq,
            CExpr::call(
                ctx.name_ref("helper"),
                vec![ctx.name_ref("rax_1")],
            ),
            CExpr::IntLit(0),
        );

        assert_eq!(
            ctx.normalize_assignment_predicate_rhs(predicate),
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::call(
                    ctx.name_ref("helper"),
                    vec![ctx.name_ref("loc")],
                ),
                CExpr::IntLit(0),
            ),
            "call expressions are not source provenance, but source-backed children still rewrite"
        );
    }

    #[test]
    fn predicate_owner_rewrite_rejects_return_register_owner() {
        let mut ctx = make_x86_64_ctx();
        install_call_owner(&mut ctx, (0x1000, 2), "rax", "rax_1");

        let predicate = CExpr::binary(
            BinaryOp::Ne,
            ctx.name_ref("rax_1"),
            CExpr::IntLit(0),
        );

        assert_eq!(
            ctx.normalize_assignment_predicate_rhs(predicate.clone()),
            predicate,
            "return-register owner names must not replace the source alias in predicates"
        );
    }

    #[test]
    fn predicate_owner_rewrite_rejects_unmaterialized_low_signal_owner() {
        let mut ctx = make_x86_64_ctx();
        install_call_owner(&mut ctx, (0x1000, 2), "v3ea00", "rax_1");

        let predicate = CExpr::binary(
            BinaryOp::Eq,
            ctx.name_ref("rax_1"),
            CExpr::IntLit(0),
        );

        assert_eq!(
            ctx.normalize_assignment_predicate_rhs(predicate.clone()),
            predicate,
            "low-signal owner names are not substituted unless materialization is justified"
        );
    }

    #[test]
    fn predicate_owner_rewrite_rejects_placeholder_owner_families() {
        for owner in ["rcx_7", "buf_home", "var_8h", "local_8", "stack_8", "arg_2"] {
            let mut ctx = make_x86_64_ctx();
            install_call_owner(&mut ctx, (0x1000, 2), owner, "rax_1");

            let predicate = CExpr::binary(
                BinaryOp::Eq,
                ctx.name_ref("rax_1"),
                CExpr::IntLit(0),
            );

            assert_eq!(
                ctx.normalize_assignment_predicate_rhs(predicate.clone()),
                predicate,
                "{owner} must not be accepted as a stable predicate owner"
            );
        }
    }

    #[test]
    fn predicate_owner_rewrite_removes_deref_of_proven_visible_owner() {
        let mut ctx = make_x86_64_ctx();
        install_call_owner(&mut ctx, (0x1000, 2), "loc", "rax_1");

        let predicate = CExpr::binary(
            BinaryOp::Ne,
            CExpr::Deref(Box::new(ctx.name_ref("loc"))),
            CExpr::IntLit(0),
        );

        assert_eq!(
            ctx.normalize_assignment_predicate_rhs(predicate),
            CExpr::binary(
                BinaryOp::Ne,
                ctx.name_ref("loc"),
                CExpr::IntLit(0)
            ),
            "a visible call-result owner behind a deref should remain the canonical owner"
        );
    }

    #[test]
    fn predicate_owner_rewrite_keeps_deref_for_unowned_visible_name() {
        let ctx = make_x86_64_ctx();
        let predicate = CExpr::binary(
            BinaryOp::Ne,
            CExpr::Deref(Box::new(ctx.name_ref("loc"))),
            CExpr::IntLit(0),
        );

        assert_eq!(
            ctx.normalize_assignment_predicate_rhs(predicate.clone()),
            predicate,
            "deref removal requires explicit visible owner provenance"
        );
    }

    fn wrap_predicate_test_parens(mut expr: CExpr, count: usize) -> CExpr {
        for _ in 0..count {
            expr = CExpr::Paren(Box::new(expr));
        }
        expr
    }

    #[test]
    fn predicate_owner_rewrite_applies_at_max_operand_depth() {
        let mut ctx = make_x86_64_ctx();
        install_call_owner(&mut ctx, (0x1000, 2), "loc", "rax_1");
        let wrapper_count = MAX_PREDICATE_OPERAND_DEPTH.saturating_sub(1) as usize;

        let predicate = CExpr::binary(
            BinaryOp::Eq,
            wrap_predicate_test_parens(ctx.name_ref("rax_1"), wrapper_count),
            CExpr::IntLit(0),
        );

        assert_eq!(
            ctx.normalize_assignment_predicate_rhs(predicate),
            CExpr::binary(
                BinaryOp::Eq,
                wrap_predicate_test_parens(ctx.name_ref("loc"), wrapper_count),
                CExpr::IntLit(0),
            ),
            "owner aliases at exactly the maximum predicate depth must still rewrite"
        );
    }

    #[test]
    fn predicate_owner_rewrite_refuses_beyond_max_operand_depth() {
        let mut ctx = make_x86_64_ctx();
        install_call_owner(&mut ctx, (0x1000, 2), "loc", "rax_1");
        let wrapper_count = MAX_PREDICATE_OPERAND_DEPTH as usize;

        let predicate = CExpr::binary(
            BinaryOp::Eq,
            wrap_predicate_test_parens(ctx.name_ref("rax_1"), wrapper_count),
            CExpr::IntLit(0),
        );

        assert_eq!(
            ctx.normalize_assignment_predicate_rhs(predicate.clone()),
            predicate,
            "owner aliases beyond the predicate depth budget must not be rewritten"
        );
    }

    #[test]
    fn predicate_owner_rewrite_refuses_deep_call_argument_beyond_max_operand_depth() {
        let mut ctx = make_x86_64_ctx();
        install_call_owner(&mut ctx, (0x1000, 2), "loc", "rax_1");
        let wrapper_count = MAX_PREDICATE_OPERAND_DEPTH.saturating_sub(1) as usize;

        let predicate = CExpr::binary(
            BinaryOp::Eq,
            CExpr::call(
                ctx.name_ref("helper"),
                vec![wrap_predicate_test_parens(
                    ctx.name_ref("rax_1"),
                    wrapper_count,
                )],
            ),
            CExpr::IntLit(0),
        );

        assert_eq!(
            ctx.normalize_assignment_predicate_rhs(predicate.clone()),
            predicate,
            "call-argument owner aliases beyond the predicate depth budget must not be rewritten"
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
                space: r2il::SpaceId::Ram,
                addr: loc_slot.clone(),
                val: loc_store,
            },
            SSAOp::Load {
                dst: loc_load.clone(),
                space: r2il::SpaceId::Ram,
                addr: loc_slot,
            },
            SSAOp::Copy {
                dst: make_var("rax", 4, 8),
                src: loc_load,
            },
            SSAOp::Load {
                dst: byte_load.clone(),
                space: r2il::SpaceId::Ram,
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
                CExpr::Deref(inner) if matches!(inner.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "loc")
            ) || matches!(
                &byte_expr,
                CExpr::Subscript { base, index }
                    if matches!(base.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "loc")
                        && matches!(index.as_ref(), CExpr::IntLit(0))
            ) || matches!(
                &byte_expr,
                CExpr::Deref(inner) if matches!(inner.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "rax_2")
            ) || matches!(
                &byte_expr,
                CExpr::Deref(inner)
                    if matches!(
                        inner.as_ref(),
                        CExpr::Cast { expr, .. }
                            if matches!(expr.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "rax_2" || &*ctx.spelling(*name) == "loc")
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
            !matches!(resolved_byte_expr, CExpr::Var(ref name) if &*ctx.spelling(*name) == "loc"),
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
            !matches!(widened_expr, CExpr::Var(ref name) if &*ctx.spelling(*name) == "loc"),
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
            !matches!(byte_return_expr, CExpr::Var(ref name) if &*ctx.spelling(*name) == "loc"),
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
            !matches!(final_ret_expr, CExpr::Var(ref name) if &*ctx.spelling(*name) == "loc"),
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
    fn x86_prepared_second_call_result_owner_survives_prior_stack_backed_call_result() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([
            (0x401140, "sym.imp.strlen".to_string()),
            (0x401190, "sym.imp.malloc".to_string()),
        ])));
        install_minimal_import_callee_facts(
            &mut ctx,
            &[(0x401140, "sym.imp.strlen"), (0x401190, "sym.imp.malloc")],
        );
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
                space: r2il::SpaceId::Ram,
                addr: s_slot.clone(),
                val: make_var("rdi", 0, 8),
            },
            SSAOp::Load {
                dst: s_load.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: len_slot.clone(),
                val: make_var("rax", 2, 8),
            },
            SSAOp::Load {
                dst: len_load.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: dup_slot.clone(),
                val: malloc_result,
            },
            SSAOp::Load {
                dst: dup_load.clone(),
                space: r2il::SpaceId::Ram,
                addr: dup_slot,
            },
            SSAOp::Copy {
                dst: final_ret.clone(),
                src: dup_load.clone(),
            },
        ]);

        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (block.addr, 11),
                crate::analysis::PreparedCallView {
                    result_owner: Some(ctx.name_ref("dup")),
                    ..crate::analysis::PreparedCallView::default()
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        ctx.analyze_blocks(std::slice::from_ref(&block));
        assert_eq!(
            ctx.state
                .analysis_ctx
                .use_info
                .call_result_source_by_alias
                .get(&dup_load.display_name())
                .copied(),
            None,
            "prepared owner text alone must not make a stack reload authoritative call-result source evidence, got {:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias
        );
        assert_eq!(
            ctx.stable_owned_call_result_name_for_source((block.addr, 11))
                .as_deref(),
            None,
            "prepared owner text alone must not authorize stable call-result ownership without canonical facts"
        );
        assert_eq!(
            ctx.get_expr(&make_var("rax", 4, 8)),
            if ctx.get_expr(&make_var("rax", 4, 8))
                == CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("len"),
                    CExpr::IntLit(1),
                )
            {
                CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("len"),
                    CExpr::IntLit(1),
                )
            } else {
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::call(
                        ctx.name_ref("ram:401140"),
                        vec![ctx.name_ref("s")],
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
            ctx.debug_normalized_addr_from_visible_expr(&ctx.name_ref("len")),
            ctx.debug_normalized_addr_from_visible_expr(&CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("len"),
                CExpr::IntLit(1),
            ))
        );
        assert_ne!(
            ctx.get_expr(&final_ret),
            ctx.name_ref("len"),
            "final return register copy must not reuse the earlier len result when dup ownership is unproven, got {:?}; aliases={:?}; defs={:?}; semantic={:?}",
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
    fn x86_owned_strlen_call_owner_requires_source_keyed_normalization() {
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
                space: r2il::SpaceId::Ram,
                addr: s_slot.clone(),
                val: make_var("rdi", 0, 8),
            },
            SSAOp::Load {
                dst: s_load.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: len_slot,
                val: make_var("tmp:6b00", 1, 8),
            },
            SSAOp::Load {
                dst: len_load,
                space: r2il::SpaceId::Ram,
                addr: make_var("tmp:len_slot", 1, 8),
            },
        ]);

        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (block.addr, 4),
                crate::analysis::PreparedCallView {
                    result_owner: Some(ctx.name_ref("len")),
                    ..crate::analysis::PreparedCallView::default()
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        ctx.analyze_blocks(std::slice::from_ref(&block));
        let strlen_call = CExpr::call(
            ctx.name_ref("sym.imp.strlen"),
            vec![ctx.name_ref("s")],
        );
        assert_eq!(
            ctx.normalize_final_call_expr(strlen_call.clone()),
            strlen_call,
            "plain rendered-call normalization must not infer a call-result owner from expression shape"
        );
        assert_eq!(
            ctx.normalize_call_expr_for_source_call(
                (block.addr, 4),
                strlen_call,
                FinalExprNormalizeContext::Generic,
            ),
            ctx.name_ref("len"),
            "source-keyed owned strlen call expression should rewrite to len; call_sources={:?}; aliases={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state.analysis_ctx.use_info.call_result_aliases
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
        install_minimal_import_callee_facts(
            &mut ctx,
            &[
                (0x401140, "sym.imp.strlen"),
                (0x401170, "sym.imp.memcpy"),
                (0x401190, "sym.imp.malloc"),
            ],
        );
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
                space: r2il::SpaceId::Ram,
                addr: s_slot.clone(),
                val: make_var("rdi", 0, 8),
            },
            SSAOp::Load {
                dst: s_load.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: len_slot.clone(),
                val: make_var("rax", 2, 8),
            },
            SSAOp::Load {
                dst: len_load.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: dup_slot.clone(),
                val: malloc_result,
            },
            SSAOp::Load {
                dst: dup_load.clone(),
                space: r2il::SpaceId::Ram,
                addr: dup_slot.clone(),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 5, 8),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
            ctx.name_ref("dup"),
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
                space: r2il::SpaceId::Ram,
                addr: make_var("tmp:4700", 1, 8),
                val: make_var("rax", 2, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f80", 1, 8),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: make_var("tmp:4700", 2, 8),
            },
            SSAOp::Copy {
                dst: make_var("rax", 4, 8),
                src: make_var("tmp:11f80", 2, 8),
            },
            SSAOp::Load {
                dst: make_var("tmp:11e00", 1, 1),
                space: r2il::SpaceId::Ram,
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
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 1),
                crate::analysis::PreparedCallView {
                    result_owner: Some(ctx.name_ref("loc")),
                    ..crate::analysis::PreparedCallView::default()
                },
            )]),
            ..PreparedSemanticView::default()
        })));

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
                || matches!(true_expr, CExpr::Cast { expr, .. } if matches!(expr.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "loc"))
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
                ctx.name_ref("loc"),
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
    fn x86_local_branch_condition_for_calldefine_imported_result_uses_source_carrier() {
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
        assert_eq!(
            cond_expr,
            CExpr::binary(
                BinaryOp::Ne,
                ctx.name_ref("rax_2"),
                CExpr::IntLit(0),
            ),
            "calldefine imported-result branch condition must keep the source carrier instead of replaying a rendered call; call_sources={:?}; defs={:?}",
            ctx.state.analysis_ctx.use_info.call_result_source_by_alias,
            ctx.state.analysis_ctx.use_info.definitions
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
            ctx.name_ref("argv"),
            CExpr::IntLit(8),
        );
        let rendered = ctx
            .debug_render_memory_access_from_visible_expr(&expr, 8)
            .expect("pointer offset load should render");

        match rendered {
            CExpr::Subscript { base, index } => {
                assert_eq!(*base, ctx.name_ref("argv"));
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
            ctx.name_ref("b"),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("a"),
                CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("a"),
                    ctx.name_ref("a"),
                ),
            ),
            Some(4),
        );

        assert_eq!(
            expr,
            CExpr::binary(
                BinaryOp::Add,
                CExpr::binary(BinaryOp::Mul, ctx.name_ref("a"), CExpr::IntLit(3)),
                ctx.name_ref("b")
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
            ctx.name_ref("buf"),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("i"),
                ctx.name_ref("i"),
            ),
            Some(8),
        );

        assert_eq!(
            expr,
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("buf"),
                CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("i"),
                    ctx.name_ref("i")
                )
            ),
            "pointer arithmetic must not be reordered or collapsed by scalar linear normalization"
        );
    }

    #[test]
    fn test_registry_arity_resolution_does_not_authorize_name_only_arity() {
        let ctx = FoldingContext::new(64);
        assert_eq!(
            ctx.non_variadic_call_arity(&ctx.name_ref("sym.imp.strcmp")),
            None
        );
        assert_eq!(
            ctx.non_variadic_call_arity(&ctx.name_ref("sym.imp.strcmp_0")),
            None
        );
    }

    #[test]
    fn typed_known_signature_arity_wins_over_registry_arity() {
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
            ctx.non_variadic_call_arity(&ctx.name_ref("sym.imp.strcmp")),
            Some(3),
            "typed signature arity is canonical; registry evidence must not cap it"
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

        let callee = ctx.name_ref("const:401050");
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

        let callee = ctx.name_ref("sym.helper");
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
            ctx.name_ref("const:401080"),
            vec![ctx.name_ref("ptr")],
        )));
        assert!(
            !ctx.call_expr_returns_void(&CExpr::call(
                ctx.name_ref("const:401090"),
                vec![],
            ))
        );
    }

    #[test]
    fn source_call_void_detection_prefers_callsite_identity_over_rendered_name() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x2000, 1);
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym.imp.free".to_string(),
                FunctionType {
                    return_type: CType::Void,
                    params: vec![CType::void_ptr()],
                    variadic: false,
                },
            ),
            (
                "free".to_string(),
                FunctionType {
                    return_type: CType::Void,
                    params: vec![CType::void_ptr()],
                    variadic: false,
                },
            ),
        ]));
        install_indirect_callsite_identity(
            &mut ctx,
            source_call,
            "sym.local.nonvoid",
            Some(FunctionType {
                return_type: CType::Int(32),
                params: Vec::new(),
                variadic: false,
            }),
        );

        let poisoned_rendered_call = CExpr::call(
            ctx.name_ref("sym.imp.free"),
            vec![ctx.name_ref("ptr")],
        );

        assert!(
            ctx.call_expr_returns_void(&poisoned_rendered_call),
            "expression-only lookup still sees the rendered void import"
        );
        assert!(
            !ctx.source_call_expr_returns_void(source_call, &poisoned_rendered_call),
            "source-call policy must prefer typed callsite identity over a poisoned rendered name"
        );
    }

    #[test]
    fn source_call_void_detection_uses_typed_callsite_signature() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x2000, 2);
        install_indirect_callsite_identity(
            &mut ctx,
            source_call,
            "sym.imp.free",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::void_ptr()],
                variadic: false,
            }),
        );

        let rendered_unknown_call = CExpr::call(
            ctx.name_ref("sym.local.rendered_name"),
            vec![ctx.name_ref("ptr")],
        );

        assert!(
            ctx.source_call_expr_returns_void(source_call, &rendered_unknown_call),
            "typed source-call signature should be enough even when the rendered name is not"
        );
    }

    #[test]
    fn source_call_expr_type_hint_prefers_typed_callsite_identity_over_rendered_callee() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x3000, 2);
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.local.poison".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: Vec::new(),
                variadic: false,
            },
        )]));
        install_indirect_callsite_identity(
            &mut ctx,
            source_call,
            "sym.imp.malloc",
            Some(FunctionType {
                return_type: CType::void_ptr(),
                params: vec![CType::UInt(64)],
                variadic: false,
            }),
        );

        let poisoned_rendered_call = CExpr::call(
            ctx.name_ref("sym.local.poison"),
            vec![CExpr::UIntLit(16)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, poisoned_rendered_call.clone());

        assert_eq!(
            ctx.known_signature_for_callee_expr(&ctx.name_ref("sym.local.poison"))
                .map(|sig| crate::variable::type_like_to_ctype(&sig.return_type)),
            Some(CType::Int(32)),
            "expression-only lookup still sees the poisoned rendered callee"
        );
        assert_eq!(
            ctx.expr_type_hint(&poisoned_rendered_call),
            Some(CType::Int(32)),
            "source-less type hints must not infer provenance from cached call expressions"
        );
        assert_eq!(
            ctx.expr_type_hint_for_source_call(source_call, &poisoned_rendered_call),
            Some(CType::void_ptr()),
            "explicit source-call return type must outrank a poisoned rendered callee"
        );
    }

    #[test]
    fn expr_type_hint_preserves_cast_and_paren_contracts() {
        let mut ctx = make_x86_64_ctx();
        ctx.set_type_hints(HashMap::from([("value".to_string(), CType::UInt(64))]));

        assert_eq!(
            ctx.expr_type_hint(&CExpr::cast(
                CType::Int(16),
                ctx.name_ref("value")
            )),
            Some(CType::Int(16))
        );
        assert_eq!(
            ctx.expr_type_hint(&CExpr::Paren(Box::new(ctx.name_ref("value")))),
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

        let carrier = CStmt::Expr(CExpr::assign(
            ctx.name_ref("x8_9"),
            CExpr::IntLit(1),
        ));
        assert!(ctx.stmt_is_side_effect_free_versioned_register_carrier(&carrier));

        let local = CStmt::Expr(CExpr::assign(
            ctx.name_ref("var_8h"),
            CExpr::IntLit(1),
        ));
        assert!(!ctx.stmt_is_side_effect_free_versioned_register_carrier(&local));
    }


    #[test]
    fn switch_selector_simplification_uses_typed_static_table_base_names() {
        let ctx = FoldingContext::new(64);
        for base in ["sym.jump_table", "obj.jump_table", "0x401000"] {
            let expr = CExpr::Subscript {
                base: Box::new(ctx.name_ref(&base.to_string())),
                index: Box::new(ctx.name_ref("selector")),
            };
            assert_eq!(
                ctx.simplify_switch_selector_expr(expr),
                ctx.name_ref("selector"),
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
                index: Box::new(ctx.name_ref("selector")),
            };
            assert_eq!(
                ctx.simplify_switch_selector_expr(expr),
                ctx.name_ref("selector"),
            );
        }

        for base in ["table", "tmp:1000_0", "arg1"] {
            let expr = CExpr::Subscript {
                base: Box::new(ctx.name_ref(&base.to_string())),
                index: Box::new(ctx.name_ref("selector")),
            };
            assert_eq!(
                ctx.simplify_switch_selector_expr(expr.clone()),
                expr,
                "{base}"
            );
        }

        let low_signal_index = CExpr::Subscript {
            base: Box::new(ctx.name_ref("sym.jump_table")),
            index: Box::new(ctx.name_ref("tmp:idx_0")),
        };
        assert_eq!(
            ctx.simplify_switch_selector_expr(low_signal_index.clone()),
            low_signal_index
        );

        let non_old_global_kind = CExpr::Subscript {
            base: Box::new(ctx.name_ref("data.jump_table")),
            index: Box::new(ctx.name_ref("selector")),
        };
        assert_eq!(
            ctx.simplify_switch_selector_expr(non_old_global_kind.clone()),
            non_old_global_kind
        );

        let invalid_hex = CExpr::Subscript {
            base: Box::new(ctx.name_ref("0xnot_hex")),
            index: Box::new(ctx.name_ref("selector")),
        };
        assert_eq!(
            ctx.simplify_switch_selector_expr(invalid_hex.clone()),
            invalid_hex
        );
    }

    #[test]
    fn certified_switch_selector_requires_control_fact() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::register(0x10, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch).with_name("switch_selector_fact");
        let selector = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.name.eq_ignore_ascii_case("rdi") && value.var.version == 0)
            .map(|value| value.id)
            .expect("rdi selector value");
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_ssa = Some(&prepared);
        ctx.inputs.function_facts = prepared.function_facts();
        install_function_control_facts(
            &mut ctx,
            r2types::FunctionControlFacts {
                switches: BTreeMap::from([(
                    0x1000,
                    r2types::SwitchSelectorFact {
                        proof_node: r2ssa::ProofNodeId::switch_certificate(0x1000).to_string(),
                        block_addr: 0x1000,
                        selector: Some(selector),
                        cases: Vec::new(),
                        default: None,
                    },
                )]),
                ..r2types::FunctionControlFacts::default()
            },
        );
        install_test_x86_64_signature(&mut ctx);
        install_certified_function_facts(&mut ctx);

        let (expr, proof_selector) = ctx
            .resolve_switch_expr_for_block_with_selector(0x1000)
            .expect("control fact should authorize switch selector rendering");

        assert_eq!(proof_selector, Some(selector));
        assert!(
            matches!(expr, CExpr::Var(ref name) if ctx.spelling(*name).eq_ignore_ascii_case("rdi") || &*ctx.spelling(*name) == "arg0"),
            "expected selector from canonical FunctionFacts control evidence, got {expr:?}"
        );
    }

    #[test]
    fn certified_switch_selector_requires_matching_control_fact_block() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::register(0x10, 8),
        });
        let prepared =
            prepared_from_r2il_blocks(&[entry], &arch).with_name("switch_selector_wrong_block");
        let selector = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.name.eq_ignore_ascii_case("rdi") && value.var.version == 0)
            .map(|value| value.id)
            .expect("rdi selector value");
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_ssa = Some(&prepared);
        ctx.inputs.function_facts = prepared.function_facts();
        install_function_control_facts(
            &mut ctx,
            r2types::FunctionControlFacts {
                switches: BTreeMap::from([(
                    0x2000,
                    r2types::SwitchSelectorFact {
                        proof_node: r2ssa::ProofNodeId::switch_certificate(0x2000).to_string(),
                        block_addr: 0x2000,
                        selector: Some(selector),
                        cases: Vec::new(),
                        default: None,
                    },
                )]),
                ..r2types::FunctionControlFacts::default()
            },
        );
        install_certified_function_facts(&mut ctx);

        assert_eq!(
            ctx.resolve_switch_expr_for_block_with_selector(0x1000),
            None,
            "certified rendering must not reuse a single switch selector proof from a different block"
        );
    }

    #[test]
    fn typed_ssa_var_storage_filters_exclude_const_and_memory_sources() {
        let ctx = FoldingContext::new(64);
        let block = make_block(vec![
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: make_var("ram:401000", 0, 8),
                val: make_var("const:1", 0, 4),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
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
    fn typed_ssa_var_storage_filters_keep_raw_memory_and_constant_numeric() {
        let mut ctx = FoldingContext::new(64);
        ctx.set_function_names(HashMap::from([(0x401000, "target".to_string())]));

        assert_eq!(
            ctx.get_expr(&make_var("ram:401000", 0, 8)),
            ctx.name_ref("ram:401000")
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
            matches!(left.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "ram:401000_1"),
            "{left:?}"
        );
        assert!(
            matches!(right.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "value_2"),
            "{right:?}"
        );
    }

    #[test]
    fn assignment_lhs_uses_typed_ssa_kind_for_versioned_arg_carriers() {
        let ctx = FoldingContext::new(64);
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

        assert_eq!(
            lowered_lhs_for(make_var("reg:10", 2, 8)),
            ctx.name_ref("r10_2")
        );
        assert_eq!(
            lowered_lhs_for(make_var("reg:zf", 2, 1)),
            ctx.name_ref("zf_2")
        );
        assert_eq!(
            lowered_lhs_for(make_var("tmp:11f80", 2, 8)),
            ctx.name_ref("t2")
        );
        assert_eq!(
            lowered_lhs_for(make_var("unique:11f80", 2, 8)),
            ctx.name_ref("t2")
        );
        assert_eq!(
            lowered_lhs_for(make_var("TMP:11f80", 2, 8)),
            ctx.name_ref("tmp_11f80_2")
        );
        assert_eq!(
            lowered_lhs_for(make_var("reg:10", 0, 8)),
            ctx.name_ref("arg1")
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
            space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
            space: r2il::SpaceId::Ram,
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
                    ctx.name_ref(&base.display_name()),
                    CExpr::IntLit(0x30),
                ))),
                CExpr::Deref(Box::new(ctx.name_ref(&base.display_name()))),
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
                    ctx.name_ref("arg1"),
                    CExpr::IntLit(0x30),
                ))),
                CExpr::Deref(Box::new(ctx.name_ref("arg1"))),
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
            ctx.name_ref("local_8"),
        );
        ctx.state.analysis_ctx.use_info.definitions.insert(
            addr.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("arg1"),
                CExpr::binary(
                    BinaryOp::Mul,
                    ctx.name_ref("local_c"),
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
            .insert(real_index.display_name(), ctx.name_ref("local_c"));
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            real_index.display_name(),
            crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Expr(CExpr::Var(
                { let CExpr::Var(id) = ctx.name_ref("local_c") else { unreachable!() }; id },
            ))),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            load.display_name(),
            crate::analysis::SemanticValue::Load {
                space: r2il::SpaceId::Ram,
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
            matches!(index.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "local_c"),
            "typed pointer locals must not survive as subscript indices, got {expr:?}"
        );
    }

    #[test]
    fn test_semantic_load_rendering_refuses_custom_space() {
        let ctx = FoldingContext::new(64);
        let addr = crate::analysis::NormalizedAddr {
            base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(make_var(
                "tmp:addr", 1, 8,
            ))),
            index: None,
            scale_bytes: 0,
            offset_bytes: 0,
        };
        let render = |space| {
            ctx.render_semantic_value(
                &crate::analysis::SemanticValue::Load {
                    space,
                    addr: addr.clone(),
                    size: 4,
                },
                0,
                &mut HashSet::new(),
            )
            .expect("semantic load rendering")
        };

        assert!(matches!(render(SpaceId::Ram), CExpr::Deref(_)));
        assert!(matches!(
            render(SpaceId::Custom(7)),
            CExpr::Call { ref func, ref args }
                if **func == ctx.name_ref("r2s_unsupported_space_load")
                    && args.first() == Some(&CExpr::StringLit("space7".to_string()))
        ));
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
                { let CExpr::Var(id) = ctx.name_ref("len") else { unreachable!() }; id },
            ))),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            buf_value.display_name(),
            crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Expr(CExpr::Var(
                { let CExpr::Var(id) = ctx.name_ref("buf") else { unreachable!() }; id },
            ))),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            store_addr.display_name(),
            crate::analysis::SemanticValue::Load {
                space: r2il::SpaceId::Ram,
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
            matches!(base.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "buf"),
            "address-like stack slot must be the subscript base, got base={base:?} index={index:?}"
        );
        assert!(
            matches!(index.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "len"),
            "scalar stack slot must remain the subscript index, got base={base:?} index={index:?}"
        );
    }

    #[test]
    fn semantic_index_storage_filter_uses_typed_ssa_name_kind_without_lowering() {
        let ctx = FoldingContext::new(64);

        assert!(!ctx.is_semantic_index_expr(&ctx.name_ref("const:4_0")));
        assert!(!ctx.is_semantic_index_expr(&ctx.name_ref("ram:401000_0")));
        assert!(ctx.is_semantic_index_expr(&ctx.name_ref("CONST:4_0")));
        assert!(ctx.is_semantic_index_expr(&ctx.name_ref("idx_1")));
        assert!(!ctx.is_semantic_index_expr(&ctx.name_ref("stack")));
        assert!(!ctx.is_semantic_index_expr(&ctx.name_ref("saved_fp")));
        assert!(!ctx.is_semantic_index_expr(&ctx.name_ref("stack_8")));
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
                ctx.name_ref("arg1"),
                CExpr::binary(
                    BinaryOp::Mul,
                    ctx.name_ref("arg2"),
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
                space: r2il::SpaceId::Ram,
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
                ctx.name_ref("arg1"),
                CExpr::binary(
                    BinaryOp::Shl,
                    ctx.name_ref("arg2"),
                    CExpr::IntLit(2),
                ),
            ),
        );
        ctx.state.analysis_ctx.use_info.semantic_values.insert(
            dst.display_name(),
            crate::analysis::SemanticValue::Load {
                space: r2il::SpaceId::Ram,
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
            matches!(index.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "arg2"),
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
                ctx.name_ref("i"),
                ctx.name_ref("buf"),
            ),
        );

        let direct = ctx
            .indexed_pointer_add_expr(
                &CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("i"),
                    ctx.name_ref("buf"),
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
            matches!(base.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "buf"),
            "typed pointer operand must be the subscript base, got base={base:?} index={index:?}"
        );
        assert!(
            matches!(index.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "i"),
            "scalar operand must be the subscript index, got base={base:?} index={index:?}"
        );
    }

    #[test]
    fn prepared_stack_load_uses_defining_op_owner_not_current_consumer() {
        let mut arch = make_test_arch_x86_64();
        arch.add_register(RegisterDef::new("RIP", 0x30, 8));
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x20, 8),
            b: Varnode::constant(u64::MAX - 3, 8),
        });
        entry.push(R2ILOp::Load {
            dst: Varnode::unique(0x200, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        entry.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x300, 8),
            a: Varnode::register(0x20, 8),
            b: Varnode::constant(u64::MAX - 7, 8),
        });
        entry.push(R2ILOp::Load {
            dst: Varnode::unique(0x400, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x300, 8),
        });
        entry.push(R2ILOp::Return {
            target: Varnode::unique(0x400, 4),
        });
        let frame_pointer = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: 0x20,
            size: 8,
        };
        let stack_pointer = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: 0x28,
            size: 8,
        };
        let return_address = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: 0x30,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"prepared-stack-owner:v1".to_vec(),
            "sysv",
            [],
            r2ssa::SourceFunctionReturn::Void,
            [
                r2ssa::SourceStackSlotSpec::new_local(
                    r2ssa::StackAddressBase::FramePointer,
                    frame_pointer,
                    -4,
                    4,
                ),
                r2ssa::SourceStackSlotSpec::new_local(
                    r2ssa::StackAddressBase::FramePointer,
                    frame_pointer,
                    -8,
                    4,
                ),
            ],
        )
        .expect("exact typed stack interface")
        .with_return_address_storage(return_address)
        .expect("exact return-address storage")
        .with_stack_pointer_storage(stack_pointer)
        .expect("exact stack-pointer storage");
        let prepared = source_owned_fixture(
            r2ssa::SsaArtifact::for_decompile_with_interface(&[entry], Some(&arch), interface)
                .expect("typed prepared SSA should build")
                .with_name("defining_load_owner"),
        );
        let block = prepared
            .function()
            .get_block(0x1000)
            .expect("prepared entry block");
        let loads = block
            .ops
            .iter()
            .enumerate()
            .filter_map(|(op_idx, op)| match op {
                SSAOp::Load { dst, addr, .. } => Some((op_idx, dst.clone(), addr.clone())),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(loads.len(), 2, "fixture should contain two distinct loads");

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.inputs.visible_bindings = Box::leak(Box::new(vec![
            visible_stack_binding("first_slot", Some(CType::i32()), -4),
            visible_stack_binding("second_slot", Some(CType::i32()), -8),
        ]));
        ctx.current_block_addr.set(Some(0x1000));
        ctx.current_op_idx.set(Some(loads[1].0));

        let expr = ctx.render_canonical_load_expr(&loads[0].1, &loads[0].2, CType::i32());
        assert_eq!(
            expr,
            ctx.name_ref("first_slot"),
            "nested rendering must use the load definition's memory fact, not the ambient consumer op"
        );
    }

    #[test]
    fn raw_ram_address_load_ignores_symbol_map_without_typed_fact() {
        let addr = make_var("ram:404000", 0, 8);
        let dst = make_var("tmp:load", 1, 8);
        let mut ctx = FoldingContext::new(64);
        ctx.inputs.symbols = Box::leak(Box::new(HashMap::from([(
            0x404000,
            "obj.global_value".to_string(),
        )])));

        let expr = ctx.render_canonical_load_expr(&dst, &addr, CType::u64());

        assert!(
            matches!(expr, CExpr::Deref(_)),
            "raw symbol map must not authorize global load rendering, got {expr:?}"
        );
        assert!(
            !format!("{expr:?}").contains("obj.global_value"),
            "raw symbol name must not leak into executable load expression: {expr:?}"
        );
    }

    #[test]
    fn raw_ram_address_store_target_ignores_symbol_map_without_typed_fact() {
        let addr = make_var("ram:404000", 0, 8);
        let mut ctx = FoldingContext::new(64);
        ctx.inputs.symbols = Box::leak(Box::new(HashMap::from([(
            0x404000,
            "obj.global_value".to_string(),
        )])));

        let expr = ctx.render_canonical_store_target_expr(&addr, 8, CType::u64());

        assert!(
            matches!(expr, CExpr::Deref(_)),
            "raw symbol map must not authorize global store target rendering, got {expr:?}"
        );
        assert!(
            !format!("{expr:?}").contains("obj.global_value"),
            "raw symbol name must not leak into executable store target: {expr:?}"
        );
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
                ctx.name_ref("arr"),
                CExpr::binary(
                    BinaryOp::Shl,
                    CExpr::binary(
                        BinaryOp::Sub,
                        CExpr::binary(
                            BinaryOp::Shl,
                            ctx.name_ref("idx"),
                            CExpr::IntLit(3),
                        ),
                        ctx.name_ref("idx"),
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: tmp6500_1,
                val: x0.clone(),
            },
            SSAOp::IntAdd {
                dst: tmp6400_1.clone(),
                a: sp1.clone(),
                b: make_var("const:4", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: tmp6500_2,
            },
            SSAOp::IntAdd {
                dst: tmp6400_2.clone(),
                a: sp1,
                b: make_var("const:4", 0, 8),
            },
            SSAOp::Load {
                dst: tmp26b00_1.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                })) if &*ctx.spelling(*name) == "arg1"
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
    fn test_typedef_aggregate_without_layout_does_not_render_field_placeholder() {
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
            .expect("unproven aggregate access may render as raw pointer arithmetic");

        assert!(
            !matches!(rendered, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "bare typedef names must not manufacture placeholder member access, got {rendered:?}"
        );
        assert!(
            !format!("{rendered:?}").contains("f_30"),
            "bare typedef names must not manufacture f_<offset> fields, got {rendered:?}"
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
                ctx.name_ref("arg1"),
                CExpr::binary(
                    BinaryOp::Mul,
                    ctx.name_ref("arg2"),
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
            .render_access_expr_from_addr(&shape, 4, false, 0, &mut render_visited)
            .expect("normalized indexed address should render");
        assert!(
            matches!(direct, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected direct indexed-member render, got {direct:?}"
        );

        let mut render_zero_visited = HashSet::new();
        let direct_zero = ctx
            .render_access_expr_from_addr(&shape, 0, false, 0, &mut render_zero_visited)
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
                ctx.name_ref("items"),
                CExpr::binary(
                    BinaryOp::Mul,
                    ctx.name_ref("idx"),
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
                    ctx.name_ref("idx"),
                    shift_mask.clone(),
                ),
                ctx.name_ref("idx"),
            ),
            shift_mask,
        );
        let addr = CExpr::binary(
            BinaryOp::Add,
            CExpr::binary(BinaryOp::Add, ctx.name_ref("arr"), scaled_index),
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
                ctx.name_ref("arr"),
                CExpr::binary(
                    BinaryOp::Mul,
                    ctx.name_ref("idx"),
                    CExpr::IntLit(56),
                ),
            ),
        );

        let addr = CExpr::binary(
            BinaryOp::Add,
            ctx.name_ref("local_c"),
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
            ctx.name_ref("arg1"),
            CExpr::binary(
                BinaryOp::Mul,
                ctx.name_ref("arg2"),
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
            space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
    fn non_ram_load_and_store_residualize_before_stack_or_pointer_lowering() {
        let addr = make_var("tmp:space_addr", 1, 8);
        let value = make_var("tmp:space_value", 1, 4);
        let space = r2il::SpaceId::Custom(7);
        let load = SSAOp::Load {
            dst: value.clone(),
            space,
            addr: addr.clone(),
        };
        let store = SSAOp::Store {
            space,
            addr,
            val: value,
        };
        let block = make_block(vec![load.clone(), store.clone()]);
        let mut ctx = FoldingContext::new(64);
        ctx.analyze_block(&block);

        for (op, effect) in [(&load, "load"), (&store, "store")] {
            let stmt = ctx
                .op_to_stmt(op)
                .expect("non-RAM effect must remain visible");
            assert!(
                matches!(&stmt, CStmt::Comment(text)
                    if text.contains(&format!("unsupported exact memory {effect} space space7"))),
                "non-RAM {effect} must residualize, got {stmt:?}"
            );
        }
    }

    #[test]
    fn test_load_generic_deref_avoids_redundant_pointer_cast() {
        let addr = make_var("arg1", 0, 8);
        let dst = make_var("tmp:9401", 1, 4);
        let block = make_block(vec![SSAOp::Load {
            dst: dst.clone(),
            space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                CExpr::binary(BinaryOp::Sub, ctx.name_ref("x"), CExpr::IntLit(0)),
                CExpr::IntLit(0),
            ),
        );
        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Ne, ctx.name_ref("x"), CExpr::IntLit(0))
        );
    }

    #[test]
    fn test_simplify_predicate_rewrites_sub_const_cmp_zero() {
        let ctx = FoldingContext::new(64);
        let expr = CExpr::binary(
            BinaryOp::Eq,
            CExpr::binary(
                BinaryOp::Sub,
                ctx.name_ref("x"),
                CExpr::IntLit(0xdead),
            ),
            CExpr::IntLit(0),
        );
        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Eq,
                ctx.name_ref("x"),
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
                ctx.name_ref("x"),
                ctx.name_ref("y"),
            ),
            CExpr::IntLit(0),
        );
        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Ne,
                ctx.name_ref("x"),
                ctx.name_ref("y")
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
                ctx.name_ref("x"),
                CExpr::UIntLit(0xffff_ffff),
            ),
            CExpr::IntLit(0),
        );
        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Eq,
                ctx.name_ref("x"),
                CExpr::UIntLit(0xffff_ffff)
            )
        );
    }

    #[test]
    fn test_c_int_typedef_return_context_signs_32_bit_literals() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_return_type =
            Some(Box::leak(Box::new(CType::Typedef("int".to_string()))));

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
    fn typed_signed_assignment_normalizes_all_ones_literal() {
        let dst = make_var("tmp:assigned", 1, 4);
        let mut ctx = make_x86_64_ctx();
        ctx.set_type_hints(HashMap::from([(dst.display_name(), CType::i32())]));

        assert_eq!(
            ctx.assignment_rhs_with_type_policy(&dst, None, CExpr::UIntLit(0xffff_ffff)),
            CExpr::IntLit(-1)
        );
    }

    #[test]
    fn test_simplify_predicate_rewrites_ne_ge_zero_to_gt_zero() {
        let ctx = FoldingContext::new(64);
        let expr = CExpr::binary(
            BinaryOp::And,
            CExpr::binary(BinaryOp::Ne, ctx.name_ref("x"), CExpr::IntLit(0)),
            CExpr::binary(BinaryOp::Ge, ctx.name_ref("x"), CExpr::IntLit(0)),
        );
        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Gt, ctx.name_ref("x"), CExpr::IntLit(0))
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
                    CExpr::cast(CType::UInt(64), ctx.name_ref("len")),
                    CExpr::cast(CType::UInt(64), ctx.name_ref("64")),
                ),
                CExpr::binary(
                    BinaryOp::Eq,
                    ctx.name_ref("len"),
                    CExpr::IntLit(100),
                ),
            ),
        );
        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Gt,
                ctx.name_ref("len"),
                CExpr::IntLit(100)
            )
        );
    }

    #[test]
    fn test_identity_sub_zero() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::Sub,
            ctx.name_ref("x"),
            CExpr::IntLit(0),
            Some(4),
        );
        assert_eq!(simplified, ctx.name_ref("x"));
    }

    #[test]
    fn test_identity_add_zero() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::Add,
            ctx.name_ref("x"),
            CExpr::IntLit(0),
            Some(4),
        );
        assert_eq!(simplified, ctx.name_ref("x"));
    }

    #[test]
    fn test_identity_add_repeated_scaled_term() {
        let mut ctx = FoldingContext::new(64);
        ctx.set_type_hints(HashMap::from([("x".to_string(), CType::Int(32))]));
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::Add,
            ctx.name_ref("x"),
            CExpr::binary(BinaryOp::Mul, ctx.name_ref("x"), CExpr::IntLit(2)),
            Some(4),
        );
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Mul, ctx.name_ref("x"), CExpr::IntLit(3))
        );
    }

    #[test]
    fn test_identity_or_zero() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::BitOr,
            ctx.name_ref("x"),
            CExpr::IntLit(0),
            Some(4),
        );
        assert_eq!(simplified, ctx.name_ref("x"));
    }

    #[test]
    fn test_identity_xor_zero() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::BitXor,
            ctx.name_ref("x"),
            CExpr::IntLit(0),
            Some(4),
        );
        assert_eq!(simplified, ctx.name_ref("x"));
    }

    #[test]
    fn test_identity_xor_self() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::BitXor,
            ctx.name_ref("x"),
            ctx.name_ref("x"),
            Some(4),
        );
        assert_eq!(simplified, CExpr::IntLit(0));
    }

    #[test]
    fn test_identity_mul_one() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::Mul,
            ctx.name_ref("x"),
            CExpr::IntLit(1),
            Some(4),
        );
        assert_eq!(simplified, ctx.name_ref("x"));
    }

    #[test]
    fn test_identity_div_one() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::Div,
            ctx.name_ref("x"),
            CExpr::IntLit(1),
            Some(4),
        );
        assert_eq!(simplified, ctx.name_ref("x"));
    }

    #[test]
    fn test_identity_and_all_ones_with_explicit_width() {
        let ctx = FoldingContext::new(64);
        let simplified = ctx.identity_simplify_binary(
            BinaryOp::BitAnd,
            ctx.name_ref("x"),
            CExpr::UIntLit(0xffff_ffff),
            Some(4),
        );
        assert_eq!(simplified, ctx.name_ref("x"));
    }

    #[test]
    fn test_identity_negative_cases_preserved() {
        let ctx = FoldingContext::new(64);
        let sub = ctx.identity_simplify_binary(
            BinaryOp::Sub,
            ctx.name_ref("x"),
            CExpr::IntLit(1),
            Some(4),
        );
        assert_eq!(
            sub,
            CExpr::binary(BinaryOp::Sub, ctx.name_ref("x"), CExpr::IntLit(1))
        );

        let add = ctx.identity_simplify_binary(
            BinaryOp::Add,
            ctx.name_ref("x"),
            CExpr::IntLit(2),
            Some(4),
        );
        assert_eq!(
            add,
            CExpr::binary(BinaryOp::Add, ctx.name_ref("x"), CExpr::IntLit(2))
        );

        let or = ctx.identity_simplify_binary(
            BinaryOp::BitOr,
            ctx.name_ref("x"),
            CExpr::IntLit(1),
            Some(4),
        );
        assert_eq!(
            or,
            CExpr::binary(
                BinaryOp::BitOr,
                ctx.name_ref("x"),
                CExpr::IntLit(1)
            )
        );
    }

    #[test]
    fn test_noop_assignment_is_suppressed() {
        let ctx = FoldingContext::new(64);
        let lhs = ctx.name_ref("x");
        let rhs = CExpr::binary(BinaryOp::Sub, ctx.name_ref("x"), CExpr::IntLit(0));
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
            ctx.name_ref("rbp_1"),
            CExpr::IntLit(-0x40),
        )));

        assert_eq!(ctx.rewrite_stack_expr(expr), ctx.name_ref("buf"));
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
            ctx.name_ref("rbp_1"),
            CExpr::IntLit(-0x40),
        );
        assert_eq!(ctx.rewrite_stack_expr(expr), ctx.name_ref("buf"));
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
                ctx.name_ref("rbp_1"),
                CExpr::IntLit(-0x48),
            )))),
        }));

        assert_eq!(
            ctx.rewrite_stack_expr(expr),
            ctx.name_ref("user_input")
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
            ctx.name_ref("rbp_1"),
            CExpr::IntLit(-0x20),
        );
        assert_eq!(ctx.rewrite_stack_expr(expr.clone()), expr);
    }

    #[test]
    fn bound_stack_name_wins_over_legacy_encoded_offset() {
        let mut ctx = FoldingContext::new(64);
        ctx.set_external_stack_vars(HashMap::from([
            (-20, stack_var_spec("var_ch", None, Some("SP"))),
            (-12, stack_var_spec("other", None, Some("SP"))),
        ]));
        ctx.analyze_blocks(&[]);

        assert_eq!(
            ctx.rewrite_stack_expr(ctx.name_ref("var_ch")),
            ctx.name_ref("var_ch")
        );
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
    fn test_resolve_stack_var_refuses_reserved_param_stack_home_without_slot_proof() {
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

        assert_eq!(
            ctx.resolve_stack_var(-8),
            None,
            "a reserved param alias is not proof of a stack local"
        );
    }

    #[test]
    fn test_resolve_stack_var_keeps_synthetic_name_with_slot_proof() {
        let mut ctx = FoldingContext::new(64);
        ctx.set_external_stack_vars(HashMap::from([(-8, stack_var_spec("", None, Some("RBP")))]));

        assert_eq!(
            ctx.resolve_stack_var(-8),
            Some("local_8".to_string()),
            "synthetic stack names require typed stack-slot evidence"
        );
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
                ctx.name_ref("result"),
                CExpr::IntLit(25),
            ),
        );
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "result".to_string(),
            CExpr::Deref(Box::new(CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp_1"),
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
                ctx.name_ref("result"),
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
                        ctx.name_ref("rbp_1"),
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
                ctx.name_ref("result"),
                CExpr::IntLit(19),
            ),
        );
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "result".to_string(),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("arg1"),
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
            .insert("tmp:foo_2".to_string(), ctx.name_ref("local_4"));
        ctx.state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert("tmp:foo_2".to_string(), "t2".to_string());

        let resolved = ctx.lookup_definition("t2");
        assert_eq!(resolved, Some(ctx.name_ref("local_4")));
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
        assert!(
            temp_matches.contains(&"tmp:raw_2".to_string()),
            "{temp_matches:?}"
        );
        assert!(
            !temp_matches.contains(&"value_2".to_string()),
            "{temp_matches:?}"
        );

        let value_matches = ctx.ssa_names_for_lowered_temp_alias("v2");
        assert!(
            value_matches.contains(&"value_2".to_string()),
            "{value_matches:?}"
        );
        assert!(
            value_matches.contains(&"TMP:raw_2".to_string()),
            "{value_matches:?}"
        );
        assert!(
            !value_matches.contains(&"tmp:raw_2".to_string()),
            "{value_matches:?}"
        );
    }

    #[test]
    fn test_lookup_definition_prefers_forwarded_semantic_value_over_register_artifact() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("tmp:ret_1".to_string(), ctx.name_ref("rax_2"));
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("src_1".to_string(), ctx.name_ref("arg1"));
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
        assert_eq!(resolved, Some(ctx.name_ref("arg1")));
    }

    #[test]
    fn test_sf_surrogate_cycle_is_guarded() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("sf_1".to_string(), ctx.name_ref("sf_2"));
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("sf_2".to_string(), ctx.name_ref("sf_1"));

        assert!(
            !ctx.is_sf_surrogate(&ctx.name_ref("sf_1")),
            "Cyclic surrogate definitions must short-circuit without recursion overflow"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_removes_unused_pure_copy() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("t1_1"),
                ctx.name_ref("arg1"),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("t2_2"),
                ctx.name_ref("arg2"),
            )),
            CStmt::Return(Some(ctx.name_ref("t2_2"))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts.clone());
        assert_eq!(pruned.len(), 2, "Unused pure temp copy should be removed");
        assert!(
            !matches!(
                pruned.first(),
                Some(CStmt::Expr(CExpr::Binary {
                    op: BinaryOp::Assign,
                    left,
                    right: _,
                })) if left.as_ref() == &ctx.name_ref("t1_1")
            ),
            "t1_1 copy should be pruned"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_removes_sleigh_load_store_temps() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("tmp_ldxn_1"),
                ctx.name_ref("sym._debug_iomalloc_size"),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("tmp_stxn_1"),
                CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("sym._debug_iomalloc_size"),
                    ctx.name_ref("arg1"),
                ),
            )),
            CStmt::Return(Some(ctx.name_ref("arg1"))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts.clone());

        assert_eq!(
            pruned,
            vec![CStmt::Return(Some(ctx.name_ref("arg1")))]
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_removes_sleigh_memory_temps_with_call_address_artifacts() {
        let ctx = FoldingContext::new(64);
        let call_based_addr = CExpr::binary(
            BinaryOp::Add,
            CExpr::call(
                ctx.name_ref("fcn.1000"),
                vec![ctx.name_ref("ctx")],
            ),
            CExpr::IntLit(50),
        );
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("tmp_ldwn_1"),
                CExpr::deref(call_based_addr.clone()),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("tmp_stwn_1"),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::deref(call_based_addr),
                    ctx.name_ref("arg1"),
                ),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::deref(CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("x0_5"),
                    CExpr::IntLit(50),
                )),
                ctx.name_ref("arg1"),
            )),
            CStmt::Return(Some(ctx.name_ref("x0_5"))),
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
            ctx.name_ref("sym._IORWLockUnlock"),
            vec![CExpr::Subscript {
                base: Box::new(CExpr::UIntLit(0xfffffe0007d21000)),
                index: Box::new(CExpr::IntLit(367)),
            }],
        );
        let stmts = vec![
            CStmt::Expr(CExpr::assign(ctx.name_ref("x0_8"), call.clone())),
            CStmt::Return(Some(ctx.name_ref("x0_3"))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);

        assert_eq!(
            pruned,
            vec![
                CStmt::Expr(call),
                CStmt::Return(Some(ctx.name_ref("x0_3"))),
            ]
        );
    }

    #[test]
    fn prune_dead_temp_assignments_rejects_rendered_void_without_source_call_void_proof() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x3000, 0);
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym.imp.free".to_string(),
                FunctionType {
                    return_type: CType::Void,
                    params: vec![CType::void_ptr()],
                    variadic: false,
                },
            ),
            (
                "free".to_string(),
                FunctionType {
                    return_type: CType::Void,
                    params: vec![CType::void_ptr()],
                    variadic: false,
                },
            ),
        ]));
        install_indirect_callsite_identity(
            &mut ctx,
            source_call,
            "sym.local.nonvoid",
            Some(FunctionType {
                return_type: CType::Int(32),
                params: Vec::new(),
                variadic: false,
            }),
        );

        let call = CExpr::call(
            ctx.name_ref("sym.imp.free"),
            vec![ctx.name_ref("ptr")],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["value_1".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("value_1".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .use_counts
            .insert("value_1".to_string(), 1);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("value_1"),
                call.clone(),
            )),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts.clone());

        assert_eq!(
            pruned, stmts,
            "rendered void imports must not demote a non-void source-call result"
        );
    }

    #[test]
    fn prune_dead_temp_assignments_uses_target_source_for_void_result_demotion() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x3000, 1);
        ctx.set_known_function_signatures(HashMap::from([
            (
                "sym.imp.free".to_string(),
                FunctionType {
                    return_type: CType::Void,
                    params: vec![CType::void_ptr()],
                    variadic: false,
                },
            ),
            (
                "free".to_string(),
                FunctionType {
                    return_type: CType::Void,
                    params: vec![CType::void_ptr()],
                    variadic: false,
                },
            ),
        ]));
        install_callsite_resolution(
            &mut ctx,
            source_call,
            0x401000,
            "sym.imp.free",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::void_ptr()],
                variadic: false,
            }),
        );

        let call = CExpr::call(
            ctx.name_ref("sym.imp.free"),
            vec![ctx.name_ref("ptr")],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["value_1".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("value_1".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .use_counts
            .insert("value_1".to_string(), 1);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(ctx.name_ref("value_1"), call)),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts.clone());

        assert_eq!(
            pruned,
            vec![
                CStmt::Expr(CExpr::call(
                    ctx.name_ref("sym.imp.free"),
                    vec![ctx.name_ref("ptr")],
                )),
                CStmt::Return(Some(CExpr::IntLit(0))),
            ],
            "target source provenance is sufficient to demote a dead void call result"
        );
    }

    #[test]
    fn prune_dead_temp_assignments_uses_typed_source_call_void_signature() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x3000, 2);
        install_indirect_callsite_identity(
            &mut ctx,
            source_call,
            "sym.imp.free",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::void_ptr()],
                variadic: false,
            }),
        );

        let call = CExpr::call(
            ctx.name_ref("sym.local.rendered_name"),
            vec![ctx.name_ref("ptr")],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["value_1".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("value_1".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .use_counts
            .insert("value_1".to_string(), 1);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("value_1"),
                call.clone(),
            )),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);

        assert_eq!(
            pruned,
            vec![CStmt::Expr(call), CStmt::Return(Some(CExpr::IntLit(0))),],
            "typed source-call void signatures justify demoting the dead call result owner"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_keeps_source_less_duplicate_bare_replayed_call() {
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
        let call = CExpr::call(ctx.name_ref("fcn.1000"), vec![CExpr::IntLit(16)]);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        let stmts = vec![
            CStmt::Expr(CExpr::assign(ctx.name_ref("x0_3"), call.clone())),
            CStmt::Expr(call.clone()),
            CStmt::Expr(call),
            CStmt::Return(Some(ctx.name_ref("x0_3"))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);

        assert_eq!(
            pruned,
            vec![
                CStmt::Expr(CExpr::assign(
                    ctx.name_ref("x0_3"),
                    CExpr::call(ctx.name_ref("fcn.1000"), vec![CExpr::IntLit(16)]),
                )),
                CStmt::Expr(CExpr::call(
                    ctx.name_ref("fcn.1000"),
                    vec![CExpr::IntLit(16)]
                )),
                CStmt::Expr(CExpr::call(
                    ctx.name_ref("fcn.1000"),
                    vec![CExpr::IntLit(16)]
                )),
                CStmt::Return(Some(ctx.name_ref("x0_3"))),
            ],
            "bare rendered calls do not carry source provenance for deduplication"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_drops_low_signal_replayed_call_assignment() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 1);
        let call = CExpr::call(ctx.name_ref("fcn.1000"), vec![CExpr::IntLit(16)]);
        assert!(ctx.is_low_signal_visible_name("v3ea00"));
        assert!(!ctx.is_prunable_dead_binding_target("v3ea00"));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["v3ea00".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("v3ea00".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .use_counts
            .insert("v3ea00".to_string(), 1);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("v3ea00"),
                call.clone(),
            )),
            CStmt::Expr(call.clone()),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);

        assert_eq!(
            pruned,
            vec![
                CStmt::Expr(CExpr::assign(
                    ctx.name_ref("v3ea00"),
                    call.clone()
                )),
                CStmt::Expr(call),
                CStmt::Return(Some(CExpr::IntLit(0))),
            ],
            "a source-less bare rendered call does not prove the later side effect is the same source call"
        );
    }

    #[test]
    fn opaque_public_call_arg_sanitizer_hides_raw_tmp_names() {
        let ctx = make_aarch64_ctx();
        let callee = ctx.name_ref("fcn.1000");

        let normalized =
            ctx.normalize_call_arg_expr_for_callee(&callee, ctx.name_ref("tmp:2a000"));

        assert_eq!(normalized, ctx.name_ref("value_2a000"));

        let normalized =
            ctx.normalize_call_arg_expr_for_callee(&callee, ctx.name_ref("TMP:2A000"));

        assert_eq!(normalized, ctx.name_ref("value_2a000"));

        let normalized =
            ctx.normalize_call_arg_expr_for_callee(&callee, ctx.name_ref("visible_arg"));

        assert_eq!(normalized, ctx.name_ref("visible_arg"));
    }

    #[test]
    fn test_propagate_ephemeral_copies_inlines_autogenerated_stack_home_param_copy() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("local_10"),
                ctx.name_ref("v"),
            )),
            CStmt::Expr(CExpr::assign(
                CExpr::Member {
                    base: Box::new(CExpr::Subscript {
                        base: Box::new(ctx.name_ref("arr")),
                        index: Box::new(ctx.name_ref("idx")),
                    }),
                    member: "f_8".to_string(),
                },
                ctx.name_ref("local_10"),
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
            &ctx.name_ref("v"),
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
                ctx.name_ref("tmp:1"),
                ctx.name_ref("global_value"),
            )),
            CStmt::Expr(CExpr::call(ctx.name_ref("mutate_global"), vec![])),
            CStmt::Return(Some(ctx.name_ref("tmp:1"))),
        ];

        let propagated = ctx.propagate_ephemeral_copies(stmts);

        assert_eq!(
            propagated,
            vec![
                CStmt::Expr(CExpr::assign(
                    ctx.name_ref("tmp:1"),
                    ctx.name_ref("global_value"),
                )),
                CStmt::Expr(CExpr::call(ctx.name_ref("mutate_global"), vec![])),
                CStmt::Return(Some(ctx.name_ref("tmp:1"))),
            ],
            "copy aliases must not be reused across side-effecting calls"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_keeps_side_effecting_rhs() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("t1_1"),
                CExpr::call(ctx.name_ref("foo"), vec![]),
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
                ctx.name_ref("t3ea00"),
                CExpr::binary(
                    BinaryOp::Sub,
                    ctx.name_ref("len"),
                    CExpr::IntLit(64),
                ),
            )),
            CStmt::If {
                cond: CExpr::binary(
                    BinaryOp::Gt,
                    ctx.name_ref("len"),
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
    fn prune_before_structuring_keeps_stack_state_written_for_later_blocks() {
        let mut ctx = FoldingContext::new(64);
        ctx.set_external_stack_vars(HashMap::from([(
            -16,
            stack_var_spec("var_10h", Some(CType::Int(32)), Some("rbp")),
        )]));
        let assignment = CStmt::Expr(CExpr::assign(
            ctx.name_ref("var_10h"),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("var_10h"),
                CExpr::Subscript {
                    base: Box::new(ctx.name_ref("arr")),
                    index: Box::new(ctx.name_ref("i")),
                },
            ),
        ));

        let pruned = ctx.prune_dead_temp_assignments_before_structuring(vec![assignment.clone()]);

        assert_eq!(
            pruned,
            vec![assignment],
            "a per-block dead-temp pass cannot discard stack state consumed by another block"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_removes_dead_register_ssa_assignment() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("rax_6"),
                CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("rax_3"),
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
                ctx.name_ref("rax_6"),
                CExpr::call(ctx.name_ref("foo"), vec![]),
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
    fn test_prune_dead_temp_assignments_demotes_observable_return_register_call_owner() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x3000, 0);
        let call = CExpr::call(
            ctx.name_ref("sym.imp.alloc"),
            vec![CExpr::IntLit(32)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["RAX_6".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("RAX_6".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .use_counts
            .insert("RAX_6".to_string(), 1);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(ctx.name_ref("RAX_6"), call.clone())),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);

        assert_eq!(
            pruned,
            vec![CStmt::Expr(call), CStmt::Return(Some(CExpr::IntLit(0))),],
            "un-pinned dead return-register call owners demote to side-effect calls even when the source has observable aliases"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_keeps_pinned_return_register_call_owner() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x3000, 1);
        let call = CExpr::call(
            ctx.name_ref("sym.imp.alloc"),
            vec![CExpr::IntLit(32)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["RAX_6".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("RAX_6".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .pinned
            .insert("rax_6".to_string());
        let stmts = vec![
            CStmt::Expr(CExpr::assign(ctx.name_ref("RAX_6"), call.clone())),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts.clone());

        assert_eq!(
            pruned, stmts,
            "pinned return-register call owners are materialized facts and must not be demoted to bare calls"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_treats_case_variant_call_owner_as_live_target() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x3000, 2);
        let call = CExpr::call(
            ctx.name_ref("sym.imp.alloc"),
            vec![CExpr::IntLit(32)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["RAX_6".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("RAX_6".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        let stmts = vec![
            CStmt::Expr(CExpr::assign(ctx.name_ref("RAX_6"), call.clone())),
            CStmt::Return(Some(ctx.name_ref("rax_6"))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts.clone());

        assert_eq!(
            pruned, stmts,
            "case variants of the same source-keyed call-result owner are live uses, not distinct replacement owners"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_ignores_non_live_distinct_call_owner_alias() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x3000, 3);
        let call = CExpr::call(
            ctx.name_ref("sym.imp.alloc"),
            vec![CExpr::IntLit(32)],
        );
        ctx.state.analysis_ctx.use_info.call_result_aliases.insert(
            source_call,
            BTreeSet::from(["value_1".to_string(), "value_2".to_string()]),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("value_1".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("value_1"),
                call.clone(),
            )),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);

        assert_eq!(
            pruned,
            vec![CStmt::Expr(call), CStmt::Return(Some(CExpr::IntLit(0))),],
            "a distinct call-result alias only justifies dropping a replayed call when that alias is live"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_keeps_stack_backed_call_result_owner() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x3000, 4);
        let source_id = CallSiteId::from(source_call);
        let call = CExpr::call(
            ctx.name_ref("sym.imp.alloc"),
            vec![CExpr::IntLit(64)],
        );
        ctx.state.analysis_ctx.ownership.call_ownership.insert(
            source_id,
            CallOwnershipFact {
                source: source_id,
                owner: Some(CallOwner {
                    visible_name: "value_1".to_string(),
                    kind: CallOwnerKind::StableLocal,
                }),
                aliases: BTreeSet::new(),
                direct_aliases: BTreeSet::new(),
            },
        );
        ctx.state
            .analysis_ctx
            .ownership
            .visible_owner_sources
            .insert("value_1".to_string(), source_id);
        ctx.state
            .analysis_ctx
            .use_info
            .stack_slots
            .insert("value_1".to_string(), StackSlotProvenance::new(-8));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("value_1"),
                call.clone(),
            )),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts.clone());

        assert_eq!(
            pruned, stmts,
            "stack-backed visible call-result owners are canonical facts and must not be demoted"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_keeps_side_effecting_non_memory_sleigh_temp_rhs() {
        let ctx = FoldingContext::new(64);
        let rhs = CExpr::binary(
            BinaryOp::Add,
            CExpr::call(ctx.name_ref("foo"), vec![]),
            CExpr::IntLit(1),
        );
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("tmp_ldwn_1"),
                rhs.clone(),
            )),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts.clone());

        assert_eq!(
            pruned, stmts,
            "Sleigh memory-temp cleanup must not drop non-memory RHS expressions that contain calls"
        );
    }

    #[test]
    fn test_prune_dead_temp_assignments_removes_dead_flag_artifacts() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("tmpng_1"),
                CExpr::binary(BinaryOp::Lt, ctx.name_ref("sp"), CExpr::IntLit(0)),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("tmpzr_1"),
                CExpr::binary(BinaryOp::Eq, ctx.name_ref("sp"), CExpr::IntLit(0)),
            )),
            CStmt::Return(Some(CExpr::Subscript {
                base: Box::new(CExpr::cast(
                    CType::ptr(CType::UInt(32)),
                    ctx.name_ref("arg1"),
                )),
                index: Box::new(ctx.name_ref("arg2")),
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
                ctx.name_ref("local_c"),
                ctx.name_ref("arg2"),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("local_10"),
                ctx.name_ref("arg3"),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("stack_8"),
                ctx.name_ref("arg1"),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("stack"),
                ctx.name_ref("arg2"),
            )),
            CStmt::Return(Some(CExpr::Subscript {
                base: Box::new(CExpr::cast(
                    CType::ptr(CType::UInt(32)),
                    ctx.name_ref("arg1"),
                )),
                index: Box::new(ctx.name_ref("arg2")),
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
                ctx.name_ref("x8"),
                CExpr::Member {
                    base: Box::new(ctx.name_ref("arg1")),
                    member: "f_30".to_string(),
                },
            )),
            CStmt::Return(Some(CExpr::binary(
                BinaryOp::Add,
                CExpr::Member {
                    base: Box::new(ctx.name_ref("arg1")),
                    member: "f_30".to_string(),
                },
                CExpr::Member {
                    base: Box::new(ctx.name_ref("arg1")),
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
                ctx.name_ref("obj.global_counter"),
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
    fn test_prune_dead_temp_assignments_keeps_semantic_global_call_assignment() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("obj.global_counter"),
                CExpr::call(ctx.name_ref("foo"), vec![]),
            )),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts.clone());

        assert_eq!(
            pruned, stmts,
            "semantic/global-like call assignments are observable effects, not transient call-result carriers"
        );
    }

    #[test]
    fn test_propagate_ephemeral_copies_rewrites_phi_copy_residue() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("eax_2"),
                ctx.name_ref("arg1"),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("eax_3"),
                CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("eax_2"),
                    ctx.name_ref("eax_2"),
                ),
            )),
            CStmt::Return(Some(ctx.name_ref("eax_3"))),
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
                    Some((target, _)) if target == { let CExpr::Var(id) = ctx.name_ref("eax_2") else { unreachable!() }; id }
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
                ctx.name_ref("eax_2"),
                CExpr::call(ctx.name_ref("foo"), vec![]),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("eax_3"),
                CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("eax_2"),
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
                ctx.name_ref("eax_2"),
                ctx.name_ref("rdi_1"),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("rdi_1"),
                CExpr::IntLit(42),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("eax_3"),
                CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("eax_2"),
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
                ctx.name_ref("eax_2"),
                CExpr::Cast {
                    ty: CType::Int(64),
                    expr: Box::new(ctx.name_ref("arg1")),
                },
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("eax_3"),
                CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("eax_2"),
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
                } if matches!(left.as_ref(), CExpr::Cast { expr, .. } if matches!(expr.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "arg1"))
            ),
            "Cast(Var(...)) should be propagated as a cheap copy RHS"
        );
    }

    #[test]
    fn test_propagate_ephemeral_copies_keeps_semantic_member_base() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("tmp:base_1"),
                ctx.name_ref("rdx_2"),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("eax_3"),
                CExpr::PtrMember {
                    base: Box::new(ctx.name_ref("tmp:base_1")),
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
                    if matches!(base.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "tmp:base_1")
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
            dst: make_var("arg0", 0, 4),
            src: make_var("EDI", 0, 4),
        });
        assert!(
            stmt.is_none(),
            "arg0 = edi entry alias copy should be suppressed"
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
            ctx.name_ref("arg0"),
            ctx.name_ref("edi"),
        );
        assert!(
            stmt.is_none(),
            "arg0 = edi should be suppressed even after non-copy normalization paths"
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
            CExpr::binary(BinaryOp::Ne, ctx.name_ref("a"), CExpr::IntLit(0)),
            CExpr::binary(
                BinaryOp::Eq,
                ctx.name_ref("of_1"),
                CExpr::binary(BinaryOp::Lt, ctx.name_ref("a"), CExpr::IntLit(0)),
            ),
        );

        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Gt, ctx.name_ref("a"), CExpr::IntLit(0))
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
            CExpr::binary(BinaryOp::Ne, ctx.name_ref("a"), CExpr::IntLit(0)),
            CExpr::binary(
                BinaryOp::Eq,
                ctx.name_ref("of_1"),
                CExpr::binary(
                    BinaryOp::Lt,
                    CExpr::cast(CType::Int(32), ctx.name_ref("a")),
                    CExpr::cast(CType::Int(32), CExpr::IntLit(0)),
                ),
            ),
        );

        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Gt, ctx.name_ref("a"), CExpr::IntLit(0))
        );
    }

    #[test]
    fn test_extract_flag_name_requires_strict_token_match() {
        let ctx = FoldingContext::new(64);
        assert_eq!(
            ctx.extract_of(&ctx.name_ref("of_12")),
            Some("of_12".to_string())
        );
        assert_eq!(ctx.extract_of(&ctx.name_ref("offset_1")), None);
        assert_eq!(ctx.extract_of(&ctx.name_ref("proof")), None);
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
            ctx.name_ref("of_2"),
            CExpr::binary(
                BinaryOp::Lt,
                CExpr::binary(
                    BinaryOp::Sub,
                    ctx.name_ref("a"),
                    ctx.name_ref("b"),
                ),
                CExpr::IntLit(0),
            ),
        );

        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Ge,
                ctx.name_ref("a"),
                ctx.name_ref("b")
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
            ctx.name_ref("of_3"),
            CExpr::binary(
                BinaryOp::Lt,
                CExpr::binary(
                    BinaryOp::Sub,
                    ctx.name_ref("a"),
                    ctx.name_ref("b"),
                ),
                CExpr::IntLit(0),
            ),
        );

        let simplified = ctx.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Lt,
                ctx.name_ref("a"),
                ctx.name_ref("b")
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

        let eq = ctx.simplify_condition_expr(ctx.name_ref("zf_7"));
        let ne =
            ctx.simplify_condition_expr(CExpr::unary(UnaryOp::Not, ctx.name_ref("zf_7")));

        assert_eq!(
            eq,
            CExpr::binary(
                BinaryOp::Eq,
                ctx.name_ref("result"),
                CExpr::IntLit(25)
            )
        );
        assert_eq!(
            ne,
            CExpr::binary(
                BinaryOp::Ne,
                ctx.name_ref("result"),
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

        let lt = ctx.simplify_condition_expr(ctx.name_ref("cf_1"));
        let ge =
            ctx.simplify_condition_expr(CExpr::unary(UnaryOp::Not, ctx.name_ref("cf_1")));
        let le = ctx.simplify_condition_expr(CExpr::binary(
            BinaryOp::Or,
            ctx.name_ref("cf_1"),
            ctx.name_ref("zf_1"),
        ));
        let gt = ctx.simplify_condition_expr(CExpr::binary(
            BinaryOp::And,
            CExpr::unary(UnaryOp::Not, ctx.name_ref("cf_1")),
            CExpr::unary(UnaryOp::Not, ctx.name_ref("zf_1")),
        ));

        assert_eq!(
            lt,
            CExpr::binary(BinaryOp::Lt, ctx.name_ref("x"), CExpr::IntLit(10))
        );
        assert_eq!(
            ge,
            CExpr::binary(BinaryOp::Ge, ctx.name_ref("x"), CExpr::IntLit(10))
        );
        assert_eq!(
            le,
            CExpr::binary(BinaryOp::Le, ctx.name_ref("x"), CExpr::IntLit(10))
        );
        assert_eq!(
            gt,
            CExpr::binary(BinaryOp::Gt, ctx.name_ref("x"), CExpr::IntLit(10))
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
            ctx.name_ref("cf_1"),
            ctx.name_ref("zf_1"),
        ));
        let gt = ctx.simplify_condition_expr(CExpr::unary(
            UnaryOp::Not,
            CExpr::binary(
                BinaryOp::Or,
                ctx.name_ref("cf_1"),
                ctx.name_ref("zf_1"),
            ),
        ));

        assert_eq!(
            le,
            CExpr::binary(
                BinaryOp::Le,
                ctx.name_ref("len"),
                CExpr::IntLit(100)
            )
        );
        assert_eq!(
            gt,
            CExpr::binary(
                BinaryOp::Gt,
                ctx.name_ref("len"),
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
                ctx.name_ref("arg0"),
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
            CExpr::binary(BinaryOp::Ne, ctx.name_ref("x"), CExpr::IntLit(0)),
            CExpr::binary(
                BinaryOp::Eq,
                ctx.name_ref("of_4"),
                CExpr::binary(BinaryOp::Lt, ctx.name_ref("y"), CExpr::IntLit(0)),
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
                space: r2il::SpaceId::Ram,
                addr: addr.clone(),
                val: arg_copy,
            },
            SSAOp::Load {
                dst: loaded.clone(),
                space: r2il::SpaceId::Ram,
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

        assert_eq!(ctx.stack_vars_map().get(&-4), Some(&"arg0".to_string()));

        let mut visited = HashSet::new();
        let resolved =
            ctx.resolve_predicate_operand(&ctx.name_ref(&loaded.display_name()), 0, &mut visited);
        assert_eq!(resolved, ctx.name_ref("arg0"));
    }

    #[test]
    fn stack_frame_op_uses_typed_temp_for_indirect_callee_saved_push() {
        let mut ctx = FoldingContext::new(64);
        let addr = make_var("tmp:stack", 1, 8);
        let saved = make_var("TMP:saved", 1, 8);
        // The temp has to point into the frame. Accepting any temp is what let
        // a field load into a callee-saved register pass as an epilogue pop.
        ctx.state.analysis_ctx.use_info.definitions.insert(
            addr.display_name(),
            CExpr::binary(BinaryOp::Sub, ctx.name_ref("rsp"), CExpr::IntLit(0x20)),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .copy_sources
            .insert(saved.display_name(), "RBX_1".to_string());

        assert!(ctx.is_stack_frame_op(&SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr: addr.clone(),
            val: saved,
        }));
        assert!(!ctx.is_stack_frame_op(&SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr,
            val: make_var("value", 1, 8),
        }));
        assert!(!ctx.is_stack_frame_op(&SSAOp::Store {
            space: r2il::SpaceId::Custom(7),
            addr: make_var("RSP", 1, 8),
            val: make_var("RBP", 1, 8),
        }));
        assert!(!ctx.is_stack_frame_op(&SSAOp::Load {
            dst: make_var("RBP", 2, 8),
            space: r2il::SpaceId::Custom(7),
            addr: make_var("RSP", 1, 8),
        }));
        // A field load into a callee-saved register through a temp that does
        // not point into the frame is program text, not an epilogue restore.
        let field = make_var("tmp:field", 1, 8);
        ctx.state.analysis_ctx.use_info.definitions.insert(
            field.display_name(),
            CExpr::binary(BinaryOp::Add, ctx.name_ref("RBX_1"), CExpr::IntLit(0x38)),
        );
        assert!(!ctx.is_stack_frame_op(&SSAOp::Load {
            dst: make_var("RBX", 2, 8),
            space: r2il::SpaceId::Ram,
            addr: field,
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
                ctx.name_ref("rax_1"),
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
                CExpr::Var({ let CExpr::Var(id) = ctx.name_ref(&first_owner.display_name()) else { unreachable!() }; id }.to_ascii_lowercase()),
                CExpr::IntLit(0),
            ),
            "second-call null check must not collapse to the first call owner"
        );
        assert!(
            branch_cond
                == CExpr::binary(
                    BinaryOp::Eq,
                    CExpr::Var({ let CExpr::Var(id) = ctx.name_ref(&second_owner.display_name()) else { unreachable!() }; id }.to_ascii_lowercase()),
                    CExpr::IntLit(0),
                )
                || matches!(
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
            ctx.name_ref("arg1"),
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
    fn call_owner_lookup_rejects_poisoned_definition_when_typed_callee_disagrees() {
        let mut ctx = make_aarch64_ctx();
        let source_call = (0x1000, 0);
        install_callsite_resolution(
            &mut ctx,
            source_call,
            0x401000,
            "sym.imp.one_arg",
            Some(FunctionType {
                return_type: CType::Void,
                params: vec![CType::Int(32)],
                variadic: false,
            }),
        );
        let poisoned_call = CExpr::call(
            ctx.name_ref("sym.local_two_arg"),
            vec![CExpr::IntLit(16)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, poisoned_call.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("X20_1".to_string(), poisoned_call.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .use_counts
            .insert("x20_1".to_string(), 1);

        assert_eq!(
            ctx.stable_owned_call_result_expr_for_source(source_call),
            None,
            "source-backed definition matching must use the typed callsite identity, not poisoned rendered-call equality"
        );
        assert_eq!(
            ctx.materializable_call_result_expr_for_call_expr(source_call, &poisoned_call),
            None,
            "explicit materialization must not accept a definition whose callee contradicts the typed source call"
        );
    }

    fn source_backed_matching_definition_without_certificate(
        source_arg: CExpr,
        definition_arg: CExpr,
    ) -> Option<CExpr> {
        let mut ctx = make_aarch64_ctx();
        let source_call = (0x1000, 0);
        let source_expr = CExpr::call(ctx.name_ref("fcn.1000"), vec![source_arg]);
        let definition_expr = CExpr::call(ctx.name_ref("fcn.1000"), vec![definition_arg]);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, source_expr.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("X20_1".to_string(), definition_expr);
        ctx.state
            .analysis_ctx
            .use_info
            .use_counts
            .insert("x20_1".to_string(), 1);

        ctx.materializable_call_result_expr_for_call_expr(source_call, &source_expr)
    }

    #[test]
    fn call_owner_lookup_requires_argument_match() {
        assert_eq!(
            source_backed_matching_definition_without_certificate(
                CExpr::IntLit(1),
                CExpr::IntLit(2)
            ),
            None,
            "source-expression similarity must not authorize result ownership"
        );
    }

    #[test]
    fn call_owner_lookup_requires_argument_count_match() {
        let mut ctx = make_aarch64_ctx();
        let source_call = (0x1000, 0);
        let source_expr = CExpr::call(
            ctx.name_ref("fcn.1000"),
            vec![CExpr::IntLit(1), CExpr::IntLit(2)],
        );
        let definition_expr =
            CExpr::call(ctx.name_ref("fcn.1000"), vec![CExpr::IntLit(1)]);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, source_expr.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("X20_1".to_string(), definition_expr);
        ctx.state
            .analysis_ctx
            .use_info
            .use_counts
            .insert("x20_1".to_string(), 1);

        assert_eq!(
            ctx.materializable_call_result_expr_for_call_expr(source_call, &source_expr),
            None,
            "source-backed owner recovery must reject definitions with a different call arity"
        );
    }

    #[test]
    fn call_owner_lookup_rejects_temporary_public_value_alias_args_without_certificate() {
        let symbols = test_table();
        assert_eq!(
            source_backed_matching_definition_without_certificate(
                crate::symbol::var_ref(&symbols, "value_2a000"),
                crate::symbol::var_ref(&symbols, "tmp:2a000"),
            ),
            None,
            "temporary SSA/public value equivalence is not call-result owner evidence"
        );
    }

    #[test]
    fn call_owner_lookup_rejects_binary_arg_matching_without_certificate() {
        let symbols = test_table();
        let source_arg = CExpr::binary(
            BinaryOp::Add,
            crate::symbol::var_ref(&symbols, "value_2a000"),
            CExpr::IntLit(1),
        );
        let matching_arg = CExpr::binary(
            BinaryOp::Add,
            crate::symbol::var_ref(&symbols, "tmp:2a000"),
            CExpr::IntLit(1),
        );
        assert_eq!(
            source_backed_matching_definition_without_certificate(source_arg.clone(), matching_arg),
            None,
            "binary call-arg equivalence must not manufacture result ownership"
        );

        let wrong_operator = CExpr::binary(
            BinaryOp::Sub,
            crate::symbol::var_ref(&symbols, "tmp:2a000"),
            CExpr::IntLit(1),
        );
        assert_eq!(
            source_backed_matching_definition_without_certificate(
                source_arg.clone(),
                wrong_operator,
            ),
            None,
            "binary call-arg text does not authorize result ownership"
        );

        let wrong_left = CExpr::binary(
            BinaryOp::Add,
            crate::symbol::var_ref(&symbols, "other"),
            CExpr::IntLit(1),
        );
        assert_eq!(
            source_backed_matching_definition_without_certificate(source_arg.clone(), wrong_left),
            None,
            "binary call-arg text does not authorize result ownership"
        );

        let wrong_right = CExpr::binary(
            BinaryOp::Add,
            crate::symbol::var_ref(&symbols, "tmp:2a000"),
            CExpr::IntLit(2),
        );
        assert_eq!(
            source_backed_matching_definition_without_certificate(source_arg, wrong_right),
            None,
            "binary call-arg text does not authorize result ownership"
        );
    }

    #[test]
    fn call_owner_lookup_rejects_cast_and_paren_call_args_without_certificate() {
        let symbols = test_table();
        assert_eq!(
            source_backed_matching_definition_without_certificate(
                crate::symbol::var_ref(&symbols, "value_2a000"),
                CExpr::cast(CType::Int(64), crate::symbol::var_ref(&symbols, "tmp:2a000")),
            ),
            None,
            "casts around matching call args are not ownership evidence"
        );
        assert_eq!(
            source_backed_matching_definition_without_certificate(
                crate::symbol::var_ref(&symbols, "value_2a000"),
                CExpr::Paren(Box::new(crate::symbol::var_ref(&symbols, "tmp:2a000"))),
            ),
            None,
            "parens around matching call args are not ownership evidence"
        );
    }

    #[test]
    fn call_owner_lookup_rejects_source_backed_matching_register_definition_without_certificate() {
        let mut ctx = make_aarch64_ctx();
        let source_call = (0x1000, 0);
        let helper_call = CExpr::call(ctx.name_ref("fcn.1000"), vec![CExpr::IntLit(16)]);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, helper_call.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("X20_1".to_string(), helper_call.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .use_counts
            .insert("x20_1".to_string(), 1);

        assert_eq!(
            ctx.stable_owned_call_result_expr_for_source(source_call),
            None,
            "source-keyed rendered definition matching must not recover a register owner"
        );
        assert_eq!(
            ctx.materializable_call_result_expr_for_call_expr(source_call, &helper_call),
            None,
            "materialization must require canonical owner evidence, not matching rendered calls"
        );
    }

    #[test]
    fn typed_callee_identity_controls_return_register_owner_policy() {
        let cases = [
            ("ram:401000_0", false),
            ("const:401000", false),
            ("sym.imp.helper", false),
            ("imp.helper", false),
            ("fcn.1000", false),
            ("sym.helper", false),
        ];

        for (idx, (callee, expected)) in cases.into_iter().enumerate() {
            let mut ctx = make_aarch64_ctx();
            let source_call = (0x1000 + idx as u64, 0);
            ctx.state.analysis_ctx.use_info.call_result_exprs.insert(
                source_call,
                CExpr::call(ctx.name_ref(&callee.to_string()), vec![]),
            );

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
        ctx.state.analysis_ctx.use_info.call_result_exprs.insert(
            source_call,
            CExpr::call(ctx.name_ref("sym.helper"), vec![]),
        );

        assert!(
            !ctx.source_call_allows_return_register_owner(source_call),
            "known-signature callees already have typed return facts and must not fall back to return-register ownership",
        );

        let mut ctx = make_aarch64_ctx();
        let source_call = (0x3000, 0);
        install_callsite_resolution(&mut ctx, source_call, 0x401000, "sym.imp.helper", None);
        ctx.state.analysis_ctx.use_info.call_result_exprs.insert(
            source_call,
            CExpr::call(ctx.name_ref("sym.local_wrapper"), vec![]),
        );

        assert!(
            !ctx.source_call_allows_return_register_owner(source_call),
            "typed imported callsite identity must override an internal-looking rendered callee name",
        );
    }

    #[test]
    fn uncertified_internal_call_rejects_return_register_owner_fallback_without_facts() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x1000, 0);
        install_callsite_resolution(&mut ctx, source_call, 0x401000, "sym.local.internal", None);
        ctx.state.analysis_ctx.use_info.call_result_exprs.insert(
            source_call,
            CExpr::call(ctx.name_ref("sym.local.internal"), Vec::new()),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["RAX_1".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .direct_call_result_aliases
            .insert("RAX_1".to_string());

        assert!(
            ctx.source_call_allows_return_register_owner(source_call),
            "typed internal identity may classify the call but cannot prove result ownership"
        );
        assert_eq!(
            ctx.fallback_owned_call_result_return_name_for_source(source_call),
            None,
            "return-register call-result ownership must come from FunctionFacts, not a direct alias fallback"
        );
        assert_eq!(
            ctx.stable_owned_call_result_name_for_source(source_call),
            None,
            "missing call-result owner facts must not invent rax as a stable owner"
        );
    }

    #[test]
    fn certified_internal_call_rejects_return_register_owner_fallback_without_facts() {
        let prepared = prepared_zero_arg_helper_call("certified_return_register_owner");
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_ssa = Some(&prepared);
        install_certified_function_facts(&mut ctx);
        let source_call = (0x1000, 1);
        install_callsite_resolution(&mut ctx, source_call, 0x401050, "sym.local.internal", None);
        ctx.state.analysis_ctx.use_info.call_result_exprs.insert(
            source_call,
            CExpr::call(ctx.name_ref("sym.local.internal"), Vec::new()),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["RAX_1".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .direct_call_result_aliases
            .insert("RAX_1".to_string());

        assert!(
            ctx.source_call_allows_return_register_owner(source_call),
            "callee identity can identify an internal call but cannot certify result ownership"
        );
        assert_eq!(
            ctx.fallback_owned_call_result_return_name_for_source(source_call),
            None,
            "certified rendering must refuse direct return-register owner fallback without FunctionFacts ownership evidence"
        );
        assert_eq!(
            ctx.stable_owned_call_result_name_for_source(source_call),
            None,
            "missing ownership evidence must residualize instead of inventing rax as a stable owner"
        );
        assert_eq!(
            ctx.materializable_call_result_expr_for_call_expr(
                source_call,
                &CExpr::call(ctx.name_ref("sym.local.internal"), Vec::new()),
            ),
            None
        );
    }

    #[test]
    fn uncertified_call_result_alias_rejects_non_return_register_owner_fallback_without_facts() {
        let mut ctx = make_aarch64_ctx();
        let source_call = (0x1000, 0);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["X20_1".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .direct_call_result_aliases
            .insert("X20_1".to_string());

        assert_eq!(
            ctx.stable_owned_call_result_name_for_source(source_call),
            None,
            "non-return register call-result ownership must come from FunctionFacts, not a direct alias fallback"
        );
    }

    #[test]
    fn certified_call_result_alias_rejects_non_return_register_owner_without_facts() {
        let arch = make_test_arch_aarch64_kernel_regs();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Call {
            target: Varnode::ram(0x401000, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("certified_non_return_register_owner");
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.prepared_ssa = Some(&prepared);
        install_certified_function_facts(&mut ctx);
        let source_call = (0x1000, 0);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["X20_1".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .direct_call_result_aliases
            .insert("X20_1".to_string());

        assert_eq!(
            ctx.stable_owned_call_result_name_for_source(source_call),
            None,
            "certified rendering must refuse direct non-return register owner fallback without FunctionFacts ownership evidence"
        );
        assert_eq!(
            ctx.should_materialize_call_result_at_source(source_call),
            None,
            "materialization must not recover a local register owner after certified ownership refused"
        );
    }

    #[test]
    fn certified_call_result_alias_accepts_prepared_function_facts_owner() {
        let prepared = prepared_zero_arg_helper_call_with_stack_slot(
            "certified_prepared_owner",
            r2ssa::StackAddressBase::StackPointer,
            -8,
        );
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_ssa = Some(&prepared);
        let source_call = (0x1000, 1);
        let call_result_facts =
            test_call_result_facts_with_owner_for_source(&prepared, source_call);
        install_stack_owner_function_facts(
            &mut ctx,
            &prepared,
            call_result_facts,
            "helper_result",
            -8,
        );
        install_certified_function_facts(&mut ctx);
        ctx.inputs.visible_bindings = Box::leak(Box::new(vec![visible_stack_binding(
            "helper_result",
            None,
            -8,
        )]));
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                source_call,
                crate::analysis::PreparedCallView {
                    result_owner: Some(ctx.name_ref("helper_result")),
                    ..crate::analysis::PreparedCallView::default()
                },
            )]),
            ..PreparedSemanticView::default()
        })));
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["RDI_1".to_string()]));
        ctx.state
            .analysis_ctx
            .use_info
            .direct_call_result_aliases
            .insert("RDI_1".to_string());

        assert_eq!(
            ctx.stable_owned_call_result_name_for_source(source_call)
                .as_deref(),
            Some("helper_result"),
            "certified rendering must keep FunctionFacts/prepared result ownership while ignoring local alias fallback"
        );
    }

    #[test]
    fn certified_stack_home_store_suppression_requires_value_owner_fact() {
        let prepared = prepared_zero_arg_helper_call_with_stack_slot(
            "certified_stack_home_store_direct_owner",
            r2ssa::StackAddressBase::StackPointer,
            -8,
        );
        let source_call = (0x1000, 1);
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let call_result_facts =
            test_call_result_facts_with_owner_for_source(&prepared, source_call);
        install_stack_owner_function_facts(
            &mut ctx,
            &prepared,
            call_result_facts.clone(),
            "helper_result",
            -8,
        );
        let callsite = r2types::CallsiteKey {
            block_addr: source_call.0,
            op_index: source_call.1,
        };
        let mut call_render = test_call_render_facts(&prepared);
        call_render
            .by_callsite
            .get_mut(&callsite)
            .expect("call-render fact")
            .disposition = r2types::CallsiteRenderDisposition::AssignedResult;
        install_function_call_render_facts(&mut ctx, call_render);
        install_certified_function_facts(&mut ctx);
        ctx.inputs.visible_bindings = Box::leak(Box::new(vec![visible_stack_binding(
            "helper_result",
            None,
            -8,
        )]));

        let value = call_result_facts
            .results_for_site(r2types::CallsiteKey {
                block_addr: source_call.0,
                op_index: source_call.1,
            })
            .next()
            .expect("call-result fact")
            .value;
        let val = prepared.value_var(value).expect("call result var").clone();
        let addr = make_var("tmp:stack_home", 1, 8);
        ctx.state.analysis_ctx.use_info.definitions.insert(
            addr.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(-8),
            ),
        );

        assert!(
            ctx.is_materialized_call_result_stack_home_store(&addr, &val),
            "exact FunctionFacts call-result owner should suppress the redundant stack-home store"
        );
    }

    #[test]
    fn certified_visible_owner_lookup_rejects_prepared_return_register_owner() {
        let prepared = prepared_zero_arg_helper_call("certified_return_register_owner_name");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let source_call = (0x1000, 1);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        install_callsite_resolution(&mut ctx, source_call, 0x401050, "sym.helper", None);
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                source_call,
                crate::analysis::PreparedCallView {
                    result_owner: Some(ctx.name_ref("RAX_1")),
                    ..crate::analysis::PreparedCallView::default()
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        assert_eq!(
            ctx.stable_owned_call_result_name_for_source(source_call),
            None,
            "certified result owner names must reject return-register placeholders"
        );
        assert_eq!(
            ctx.source_call_for_visible_owner_name("RAX_1"),
            None,
            "rejected prepared owner names must not authorize visible source-call lookup"
        );
        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs_for_visible_name({ let CExpr::Var(id) = ctx.name_ref("RAX_1") else { unreachable!() }; id }),
            None,
            "rejected return-register owner names must not synthesize executable call replay"
        );
    }

    #[test]
    fn raw_import_name_hints_do_not_authorize_imported_call_policy() {
        let mut ctx = make_aarch64_ctx();
        assert!(!ctx.is_imported_call_target(&ctx.name_ref("sym.imp.printf")));
        assert!(!ctx.is_imported_call_target(&ctx.name_ref("imp.printf")));
        assert!(!ctx.is_imported_call_target(&ctx.name_ref("sym.helper")));
        assert!(!ctx.is_imported_call_target(&ctx.name_ref("fcn.401000")));

        ctx.set_known_function_signatures(HashMap::from([(
            "plain_helper".to_string(),
            FunctionType {
                return_type: CType::u64(),
                params: Vec::new(),
                variadic: false,
            },
        )]));

        assert!(!ctx.is_imported_call_target(&ctx.name_ref("plain_helper")));
        assert!(!ctx.is_imported_call_target(&ctx.name_ref("other_helper")));
    }

    #[test]
    fn raw_callee_fact_name_does_not_resolve_normalized_alias_without_typed_resolution() {
        let mut ctx = make_aarch64_ctx();
        install_function_callee_facts(
            &mut ctx,
            BTreeMap::from([(0x401000, minimal_callee_fact(0x401000, "sym.imp.printf"))]),
        );

        let identity = ctx.callee_identity_for_name("printf");

        assert_eq!(identity.target_addr, None);
        assert_eq!(identity.normalized_name(), "printf");
        assert!(
            !ctx.callee_target_policy_for_identity(&identity).imported,
            "raw callee facts must not resolve normalized aliases outside typed callee resolution",
        );
    }

    #[test]
    fn typed_callee_resolution_resolves_normalized_alias_without_import_policy() {
        let symbols = test_table();
        let mut ctx = make_aarch64_ctx();
        let callee_facts =
            BTreeMap::from([(0x401000, minimal_callee_fact(0x401000, "sym.imp.printf"))]);
        let function_names = HashMap::new();
        let binary_symbols = HashMap::new();
        let known_signatures = HashMap::new();
        let resolution =
            r2types::CalleeResolutionFacts::from_context(&r2types::CalleeIdentityContext {
                function_names: &function_names,
                symbols: &binary_symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_signatures,
            });
        install_function_callee_facts(&mut ctx, callee_facts);
        mutate_function_facts(&mut ctx, |function_facts| {
            function_facts.set_callee_resolution(resolution);
        });

        let identity = ctx.callee_identity_for_name("printf");

        assert_eq!(identity.target_addr, Some(0x401000));
        assert_eq!(identity.normalized_name(), "printf");
        assert!(
            !ctx.callee_target_policy_for_identity(&identity).imported,
            "typed normalized aliases resolve identity, but import-looking names are not import authority",
        );
    }

    #[test]
    fn typed_callee_resolution_authorizes_import_policy_with_explicit_linkage() {
        let symbols = test_table();
        let mut ctx = make_aarch64_ctx();
        let callee_facts = BTreeMap::from([(
            0x401000,
            minimal_import_callee_fact(0x401000, "sym.imp.printf"),
        )]);
        let function_names = HashMap::new();
        let binary_symbols = HashMap::new();
        let known_signatures = HashMap::new();
        let resolution =
            r2types::CalleeResolutionFacts::from_context(&r2types::CalleeIdentityContext {
                function_names: &function_names,
                symbols: &binary_symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_signatures,
            });
        install_function_callee_facts(&mut ctx, callee_facts);
        mutate_function_facts(&mut ctx, |function_facts| {
            function_facts.set_callee_resolution(resolution);
        });

        let identity = ctx.callee_identity_for_name("printf");

        assert_eq!(identity.target_addr, Some(0x401000));
        assert_eq!(identity.normalized_name(), "printf");
        assert!(
            ctx.callee_target_policy_for_identity(&identity).imported,
            "explicit imported linkage authorizes import policy after normalized fact lookup",
        );
    }

    #[test]
    fn callee_fact_name_fallback_rejects_empty_normalized_alias_collisions() {
        let mut ctx = make_aarch64_ctx();
        install_minimal_import_callee_facts(&mut ctx, &[(0x401000, "imp.")]);

        let identity = ctx.callee_identity_for_name("sym.imp.");

        assert_eq!(identity.target_addr, None);
        assert!(
            !ctx.callee_target_policy_for_identity(&identity).imported,
            "empty normalized aliases must not bind unrelated import-looking callee facts",
        );
    }

    #[test]
    fn call_source_proof_raw_owner_recovery_rejects_alias_owner_without_function_facts() {
        fn seed_owner(ctx: &mut FoldingContext<'_>, source_call: (u64, usize), alias: &str) {
            let symbols = test_table();
            let symbols = test_table();
            let symbols = test_table();
            let symbols = test_table();
            let symbols = test_table();
            let symbols = test_table();
            let symbols = test_table();
            let symbols = test_table();
            let symbols = test_table();
            ctx.state
                .analysis_ctx
                .use_info
                .call_result_aliases
                .insert(source_call, BTreeSet::from([alias.to_string()]));
            ctx.state
                .analysis_ctx
                .use_info
                .direct_call_result_aliases
                .insert(alias.to_string());
            ctx.state
                .analysis_ctx
                .use_info
                .use_counts
                .insert(alias.to_ascii_lowercase(), 1);
        }

        let helper_call = CExpr::call(
            ctx.name_ref("sym.imp.helper"),
            vec![ctx.name_ref("arg1")],
        );

        let mut exact_ctx = make_aarch64_ctx();
        let exact_call = (0x1000, 0);
        exact_ctx
            .state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(exact_call, helper_call.clone());
        seed_owner(&mut exact_ctx, exact_call, "X20_1");
        assert_eq!(
            exact_ctx.stable_owned_call_result_expr_for_raw_call(&helper_call),
            None,
            "one exact source proof still cannot recover a stable owner without FunctionFacts call-result ownership"
        );

        let mut ambiguous_ctx = make_aarch64_ctx();
        let first_call = (0x1000, 0);
        let second_call = (0x1008, 0);
        ambiguous_ctx
            .state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(first_call, helper_call.clone());
        ambiguous_ctx
            .state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(second_call, helper_call.clone());
        seed_owner(&mut ambiguous_ctx, first_call, "X20_1");
        seed_owner(&mut ambiguous_ctx, second_call, "X21_1");
        assert_eq!(
            ambiguous_ctx.stable_owned_call_result_expr_for_raw_call(&helper_call),
            None,
            "ambiguous source proof must not pick the first matching owner"
        );

        let unresolved_candidate = CExpr::call(
            CExpr::deref(ctx.name_ref("fp_a")),
            vec![CExpr::IntLit(1)],
        );
        let unresolved_observed = CExpr::call(
            CExpr::deref(ctx.name_ref("fp_b")),
            vec![CExpr::IntLit(1)],
        );
        let mut unresolved_ctx = make_aarch64_ctx();
        unresolved_ctx
            .state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(exact_call, unresolved_candidate);
        seed_owner(&mut unresolved_ctx, exact_call, "X20_1");
        assert_eq!(
            unresolved_ctx.stable_owned_call_result_expr_for_raw_call(&unresolved_observed),
            None,
            "different unresolved call targets must not match just because both lack identity"
        );
    }

    #[test]
    fn test_use_info_deterministic() {
        let symbols = test_table();
        let eax_0 = make_var("EAX", 0, 4);
        let tmp = make_var("tmp:8200", 1, 4);
        let block = make_block(vec![
            SSAOp::IntAdd {
                dst: tmp.clone(),
                a: eax_0,
                b: make_var("const:1", 0, 4),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: make_var("const:1000", 0, 8),
                val: tmp,
            },
        ]);

        let ctx_a = FoldingContext::new(64);
        let ctx_b = FoldingContext::new(64);
        let blocks = vec![block];

        let cfg_a = ctx_a.to_pass_env();
        let cfg_b = ctx_b.to_pass_env();
        let info_a = analysis::UseInfo::analyze(&symbols, &blocks, &cfg_a);
        let info_b = analysis::UseInfo::analyze(&symbols, &blocks, &cfg_b);
        assert_eq!(info_a, info_b, "UseInfo analysis should be deterministic");
    }

    #[test]
    fn test_flag_info_transitive_marking_and_guard() {
        let symbols = test_table();
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
        let use_info = analysis::UseInfo::analyze(&symbols, &blocks, &cfg);
        let flag_info = analysis::FlagInfo::analyze(&symbols, &blocks, &use_info, &cfg);
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
                space: r2il::SpaceId::Ram,
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
        let use_info = analysis::UseInfo::analyze(&symbols, &blocks, &cfg);
        let flag_info = analysis::FlagInfo::analyze(&symbols, &blocks, &use_info, &cfg);
        assert!(!flag_info.flag_only_values.contains(&tmp2.display_name()));
    }

    #[test]
    fn test_stack_info_arg_alias_requires_version_zero() {
        let symbols = test_table();
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
                space: r2il::SpaceId::Ram,
                addr,
                val: eax_1,
            },
        ]);

        let ctx = FoldingContext::new(64);
        let blocks = vec![block];
        let cfg = ctx.to_pass_env();
        let use_info = analysis::UseInfo::analyze(&symbols, &blocks, &cfg);
        let stack_info = analysis::StackInfo::analyze(&symbols, &blocks, &use_info, &cfg);

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
        let symbols = test_table();
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
            carrier_aliases: crate::analysis::no_carrier_aliases(),
            string_literals: crate::analysis::lower::no_string_literals(),
            ptr_size: 8,
            sp_name: "rsp",
            fp_name: "rbp",
            ret_reg_name: "rax",
            function_names: empty_u64,
            strings: empty_u64,
            binary_symbols: empty_u64,
            symbols: &test_table(),
            callee_facts: crate::analysis::empty_callee_facts(),
            callee_resolution: None,
            summary_view: None,
            arg_regs,
            param_register_aliases: empty_str,
            caller_saved_regs: empty_saved,
            type_hints: empty_ty,
            type_oracle: None,
        };

        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        let mut info = analysis::UseInfo::analyze(&symbols, &fold_blocks, &env);
        analysis::use_info::annotate_stack_slot_semantics(&symbols, 
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                    canonical_storage: None,
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
                    canonical_storage: None,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
    fn raw_x86_check_secret_like_cfg_keeps_distinct_branch_return_values_before_render() {
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
                space: r2il::SpaceId::Ram,
                addr: make_var("tmp:4700", 1, 8),
                val: make_var("tmp:6a80", 1, 4),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 1, 4),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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

        let then_preserves_return_one =
            func.get_block(0x1004).expect("then").ops.iter().any(|op| {
                matches!(
                    op,
                    SSAOp::Copy { dst, src }
                        if dst.name == "RAX"
                            && dst.version == 1
                            && src.name == "const:1"
                            && src.version == 0
                )
            });
        let else_preserves_return_zero =
            func.get_block(0x1008).expect("else").ops.iter().any(|op| {
                matches!(
                    op,
                    SSAOp::Copy { dst, src }
                        if dst.name == "RAX"
                            && dst.version == 2
                            && src.name == "const:0"
                            && src.version == 0
                )
            });

        assert!(
            then_preserves_return_one,
            "then arm should preserve the raw SSA definition RAX_1 = 1"
        );
        assert!(
            else_preserves_return_zero,
            "else arm should preserve the raw SSA definition RAX_2 = 0"
        );
    }

    #[test]
    fn folded_x86_check_secret_observed_cfg_keeps_distinct_branch_returns() {
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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

        let then_stmts = ctx.fold_block(func.get_block(0x40128a).expect("then"), 0x40128a);
        let else_stmts = ctx.fold_block(func.get_block(0x401291).expect("else"), 0x401291);
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
                ctx.name_ref("a"),
                ctx.name_ref("b")
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
                ctx.name_ref("a"),
                ctx.name_ref("b")
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
            !matches!(expr, CExpr::Var(name) if ctx.spelling(*name).eq_ignore_ascii_case("rax_0")),
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
            !matches!(expr, CExpr::Var(name) if ctx.spelling(*name).eq_ignore_ascii_case("eax_0")),
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
            matches!(expr, CExpr::Var(name) if ctx.spelling(*name).eq_ignore_ascii_case("rax_0") || name.eq_ignore_ascii_case("rax")),
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
                ctx.name_ref("rbp"),
                CExpr::IntLit(0),
            ))),
        );
        ctx.analyze_block(&block);
        let stmts = ctx.fold_block(&block, block.addr);

        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("Expected trailing return statement");
        };
        assert!(
            !matches!(expr, CExpr::Var(name) if &*ctx.spelling(*name) == "stack_0" || &*ctx.spelling(*name) == "saved_fp"),
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
            .insert(ret.display_name(), ctx.name_ref("stack"));
        ctx.analyze_block(&block);
        let stmts = ctx.fold_block(&block, block.addr);

        let Some(CStmt::Return(Some(expr))) = stmts.last() else {
            panic!("Expected trailing return statement");
        };
        assert!(
            !matches!(expr, CExpr::Var(name) if &*ctx.spelling(*name) == "stack"),
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
            .insert(ret.display_name(), ctx.name_ref("rax_0"));
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("resolved_1".to_string(), ctx.name_ref("arg1"));
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
            &ctx.name_ref("arg1"),
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
    fn certified_control_epilogue_renders_same_root_return_register_phi() {
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
        install_certified_function_facts(&mut ctx);
        ctx.analyze_blocks(&func.blocks().cloned().collect::<Vec<_>>());
        ctx.analyze_function_structure(func);

        let exit_block = func.get_block(0x100c).expect("exit block");
        let stmts = ctx.fold_block(exit_block, exit_block.addr);
        assert!(
            stmts
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(Some(CExpr::IntLit(1))))),
            "certified fold-block rendering must render same-root return-register phi through upstream proof: {stmts:?}"
        );
        assert!(
            !stmts.iter().any(|stmt| {
                matches!(stmt, CStmt::Comment(text) if text.contains("missing certified value return"))
            }),
            "same-root return-register phi should not residualize: {stmts:?}"
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: slot_arr.clone(),
                val: rdi,
            },
            SSAOp::IntAdd {
                dst: slot_idx.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_idx.clone(),
                val: esi,
            },
            SSAOp::Load {
                dst: idx_loaded.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                ctx.name_ref(&load_first.display_name()),
                ctx.name_ref(&load_second.display_name()),
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: make_var("tmp:4700", 1, 8),
                val: make_var("RDI", 0, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 2, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: make_var("tmp:4700", 2, 8),
                val: make_var("ESI", 0, 4),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 3, 8),
                a: make_var("RBP", 1, 8),
                b: make_var("const:fffffffffffffff0", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: make_var("tmp:4700", 3, 8),
                val: make_var("EDX", 0, 4),
            },
            SSAOp::Load {
                dst: make_var("tmp:11f00", 1, 4),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: make_var("tmp:4700", 5, 8),
            },
            SSAOp::IntAdd {
                dst: make_var("tmp:4700", 6, 8),
                a: make_var("RDX", 3, 8),
                b: make_var("const:34", 0, 8),
            },
            SSAOp::Load {
                dst: make_var("EAX", 2, 4),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: slot_arr.clone(),
                val: rdi,
            },
            SSAOp::IntAdd {
                dst: slot_idx.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_idx.clone(),
                val: esi,
            },
            SSAOp::Load {
                dst: arr_loaded.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                ctx.name_ref("arg1"),
                CExpr::binary(
                    BinaryOp::Mul,
                    CExpr::binary(
                        BinaryOp::Sub,
                        CExpr::binary(
                            BinaryOp::BitXor,
                            ctx.name_ref("arg4"),
                            ctx.name_ref("arg4"),
                        ),
                        ctx.name_ref("arg2"),
                    ),
                    CExpr::IntLit(4),
                ),
            ),
            4,
        );
        let normalized = ctx.debug_normalized_addr_from_visible_expr(&CExpr::binary(
            BinaryOp::Add,
            ctx.name_ref("arg1"),
            CExpr::binary(
                BinaryOp::Mul,
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::binary(
                        BinaryOp::BitXor,
                        ctx.name_ref("arg4"),
                        ctx.name_ref("arg4"),
                    ),
                    ctx.name_ref("arg2"),
                ),
                CExpr::IntLit(4),
            ),
        ));
        let canonical = ctx.debug_canonicalize_visible_address_expr(&CExpr::binary(
            BinaryOp::Add,
            ctx.name_ref("arg1"),
            CExpr::binary(
                BinaryOp::Mul,
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::binary(
                        BinaryOp::BitXor,
                        ctx.name_ref("arg4"),
                        ctx.name_ref("arg4"),
                    ),
                    ctx.name_ref("arg2"),
                ),
                CExpr::IntLit(4),
            ),
        ));
        let extracted = ctx.debug_extract_visible_scaled_index(&CExpr::binary(
            BinaryOp::Mul,
            CExpr::binary(
                BinaryOp::Sub,
                CExpr::IntLit(0),
                ctx.name_ref("arg2"),
            ),
            CExpr::IntLit(4),
        ));
        let base_norm =
            ctx.debug_normalized_addr_from_visible_expr(&ctx.name_ref("arg1"));
        let idx_norm = ctx.debug_normalized_addr_from_visible_expr(&ctx.name_ref("arg2"));
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
                space: r2il::SpaceId::Ram,
                addr: slot_arr.clone(),
                val: rdi,
            },
            SSAOp::IntAdd {
                dst: slot_idx.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_idx.clone(),
                val: esi,
            },
            SSAOp::Load {
                dst: arr_loaded.clone(),
                space: r2il::SpaceId::Ram,
                addr: slot_arr,
            },
            SSAOp::Copy {
                dst: rax1.clone(),
                src: arr_loaded,
            },
            SSAOp::Load {
                dst: idx_loaded.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                ctx.name_ref("ecx"),
                ctx.name_ref("ecx"),
            ),
        );

        let expr = CExpr::binary(
            BinaryOp::Add,
            ctx.name_ref("arg1"),
            CExpr::binary(
                BinaryOp::Mul,
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::binary(
                        BinaryOp::BitXor,
                        ctx.name_ref("ecx"),
                        ctx.name_ref("ecx"),
                    ),
                    ctx.name_ref("arg2"),
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
            ctx.name_ref("arg1"),
            CExpr::binary(
                BinaryOp::Mul,
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::IntLit(0),
                    ctx.name_ref("arg2"),
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
                space: r2il::SpaceId::Ram,
                addr: slot_obj.clone(),
                val: rdi,
            },
            SSAOp::IntAdd {
                dst: slot_val.clone(),
                a: rbp,
                b: make_var("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_val.clone(),
                val: esi,
            },
            SSAOp::Load {
                dst: val_loaded.clone(),
                space: r2il::SpaceId::Ram,
                addr: slot_val,
            },
            SSAOp::Copy {
                dst: ecx1.clone(),
                src: val_loaded,
            },
            SSAOp::Load {
                dst: obj_loaded1.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: store_addr,
                val: ecx1,
            },
            SSAOp::Load {
                dst: obj_loaded2.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: load_addr30,
            },
            SSAOp::Copy {
                dst: eax1.clone(),
                src: load30,
            },
            SSAOp::Load {
                dst: load0.clone(),
                space: r2il::SpaceId::Ram,
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
            ctx.name_ref("arg1"),
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
                space: r2il::SpaceId::Ram,
                addr: slot_obj,
                val: x0,
            },
            SSAOp::IntAdd {
                dst: slot_val.clone(),
                a: sp1.clone(),
                b: make_var("const:4", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: slot_obj_2,
            },
            SSAOp::IntAdd {
                dst: field_addr_30.clone(),
                a: x9_1,
                b: make_var("const:30", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: slot_obj_3,
            },
            SSAOp::IntAdd {
                dst: field_addr_30_load.clone(),
                a: x8_2.clone(),
                b: make_var("const:30", 0, 8),
            },
            SSAOp::Load {
                dst: load_30.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
                addr: slot_obj_4,
            },
            SSAOp::Copy {
                dst: copy_base.clone(),
                src: x9_2,
            },
            SSAOp::Load {
                dst: load_0.clone(),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                canonical_storage: None,
            },
            PhiNode {
                dst: make_var("tmp:300", 2, 4),
                sources: vec![
                    (0x100c, make_var("tmp:300", 0, 4)),
                    (0x1008, make_var("tmp:300", 0, 4)),
                ],
                canonical_storage: None,
            },
            PhiNode {
                dst: make_var("tmp:6400", 5, 8),
                sources: vec![
                    (0x100c, make_var("tmp:6400", 0, 8)),
                    (0x1008, make_var("tmp:6400", 0, 8)),
                ],
                canonical_storage: None,
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
                space: r2il::SpaceId::Ram,
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
    fn folded_observed_live_arm64_check_secret_returns_zero_and_one() {
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                canonical_storage: None,
            },
            PhiNode {
                dst: make_var("X8", 4, 8),
                sources: vec![
                    (0x1028, make_var("X8", 0, 8)),
                    (0x1014, make_var("X8", 0, 8)),
                ],
                canonical_storage: None,
            },
            PhiNode {
                dst: make_var("tmp:6400", 5, 8),
                sources: vec![
                    (0x1028, make_var("tmp:6400", 0, 8)),
                    (0x1014, make_var("tmp:6400", 0, 8)),
                ],
                canonical_storage: None,
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
                space: r2il::SpaceId::Ram,
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

        let mut ctx = make_aarch64_ctx();
        ctx.analyze_blocks(&func.blocks().cloned().collect::<Vec<_>>());
        ctx.analyze_function_structure(&func);

        let then_stmts = ctx.fold_block(func.get_block(0x1028).expect("then"), 0x1028);
        let else_stmts = ctx.fold_block(func.get_block(0x1014).expect("else"), 0x1014);
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
    fn folded_observed_live_arm64_check_secret_with_plugin_context_returns_zero_and_one() {
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                canonical_storage: None,
            },
            PhiNode {
                dst: make_var("X8", 4, 8),
                sources: vec![
                    (0x1028, make_var("X8", 0, 8)),
                    (0x1014, make_var("X8", 0, 8)),
                ],
                canonical_storage: None,
            },
            PhiNode {
                dst: make_var("tmp:6400", 5, 8),
                sources: vec![
                    (0x1028, make_var("tmp:6400", 0, 8)),
                    (0x1014, make_var("tmp:6400", 0, 8)),
                ],
                canonical_storage: None,
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
                space: r2il::SpaceId::Ram,
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

        let mut ctx = make_aarch64_ctx();
        ctx.set_external_stack_vars(HashMap::from([
            (
                8,
                stack_var_spec("var_8h", Some(crate::CType::Int(64)), Some("sp")),
            ),
            (
                12,
                stack_var_spec("var_ch", Some(crate::CType::Int(32)), Some("sp")),
            ),
        ]));
        ctx.analyze_blocks(&func.blocks().cloned().collect::<Vec<_>>());
        ctx.analyze_function_structure(&func);

        let then_stmts = ctx.fold_block(func.get_block(0x1028).expect("then"), 0x1028);
        let else_stmts = ctx.fold_block(func.get_block(0x1014).expect("else"), 0x1014);
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
                    space: r2il::SpaceId::Ram,
                    addr: make_var("tmp:6400", 1, 8),
                    val: make_var("W0", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: make_var("tmp:6400", 2, 8),
                    a: make_var("SP", 1, 8),
                    b: make_var("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
    fn folded_observed_live_arm64_check_secret_exact_shape_returns_zero_and_one() {
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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

        let mut ctx = make_aarch64_ctx();
        ctx.set_external_stack_vars(HashMap::from([(
            12,
            stack_var_spec("var_ch", Some(crate::CType::Int(32)), Some("sp")),
        )]));
        ctx.analyze_blocks(&func.blocks().cloned().collect::<Vec<_>>());
        ctx.analyze_function_structure(&func);

        let then_stmts = ctx.fold_block(func.get_block(0x1000005c0).expect("then"), 0x1000005c0);
        let else_stmts = ctx.fold_block(func.get_block(0x10000059c).expect("else"), 0x10000059c);
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
    fn folded_observed_live_arm64_main_usage_path_returns_one_not_argc() {
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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

        let mut ctx = make_aarch64_ctx();
        ctx.set_external_stack_vars(HashMap::from([(
            12,
            stack_var_spec("var_ch", Some(crate::CType::Int(32)), Some("sp")),
        )]));
        ctx.inputs.function_names = Box::leak(Box::new(HashMap::from([(
            0x10000259c,
            "sym.imp.printf".to_string(),
        )])));
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(
            0x100002638,
            "Usage: %s <test_num> [args...]\\n".to_string(),
        )])));
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([
            ("x0".to_string(), "argc".to_string()),
            ("x1".to_string(), "argv".to_string()),
        ])));
        ctx.set_known_function_signatures(HashMap::from([(
            "sym.imp.printf".to_string(),
            FunctionType {
                return_type: CType::Int(32),
                params: vec![CType::ptr(CType::Int(8))],
                variadic: true,
            },
        )]));
        ctx.analyze_blocks(&func.blocks().cloned().collect::<Vec<_>>());
        ctx.analyze_function_structure(&func);

        let usage_stmts = ctx.fold_block(func.get_block(0x1004).expect("usage"), 0x1004);
        let Some(CStmt::Return(Some(return_expr))) = usage_stmts.last() else {
            panic!("usage block should fold to return, got {usage_stmts:?}");
        };
        assert_eq!(
            ctx.state.analysis_ctx.use_info.definitions.get("X8_1"),
            Some(&CExpr::IntLit(1)),
            "usage path constant-one source should survive analysis"
        );
        assert_eq!(return_expr, &ctx.name_ref("tretcopy_1"));
        assert_ne!(return_expr, &ctx.name_ref("argc"));
    }

    #[test]
    fn aarch64_unused_helper_call_result_residualizes_without_functionfacts_call_render() {
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
        let helper_call = (block.addr, 1);
        let helper_args = ctx
            .call_args_map()
            .get(&helper_call)
            .cloned()
            .unwrap_or_default();
        insert_authorized_call_args(&mut ctx, helper_call, helper_args);
        let stmts = ctx.fold_block(&block, block.addr);
        assert!(
            matches!(
                stmts.first(),
                Some(CStmt::Comment(comment))
                    if comment.contains("uncertified callsite arguments")
            ),
            "unused helper result without FunctionFacts call-render proof should residualize, got {stmts:?}"
        );
        assert!(
            !stmts.iter().any(|stmt| matches!(
                stmt,
                CStmt::Expr(CExpr::Binary {
                    op: BinaryOp::Assign,
                    left,
                    right,
                }) if matches!(left.as_ref(), CExpr::Var(name) if ctx.spelling(*name).eq_ignore_ascii_case("x0_2"))
                    && matches!(right.as_ref(), CExpr::Call { .. })
            )),
            "unused helper result must not materialize a transient assignment, got {stmts:?}"
        );
    }

    #[test]
    fn folded_x86_complex_check_keeps_named_local_carrier_and_concrete_returns() {
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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

        let cond = ctx
            .extract_condition_from_block(func.get_block(0x1000).expect("entry"))
            .expect("complex_check predicate");
        assert!(
            matches!(
                &cond,
                CExpr::Binary {
                    op: BinaryOp::Eq | BinaryOp::Ne,
                    left,
                    right,
                } if (matches!(left.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "arg0")
                    && matches!(right.as_ref(), CExpr::IntLit(100)))
                    || (matches!(right.as_ref(), CExpr::Var(name) if &*ctx.spelling(*name) == "arg0")
                        && matches!(left.as_ref(), CExpr::IntLit(100)))
            ),
            "expected recovered arg0/100 predicate, got {cond:?}"
        );

        let one_stmts = ctx.fold_block(func.get_block(0x1004).expect("one"), 0x1004);
        let zero_stmts = ctx.fold_block(func.get_block(0x1008).expect("zero"), 0x1008);
        let Some(CStmt::Return(Some(one_expr))) = one_stmts.last() else {
            panic!("one block should fold to return, got {one_stmts:?}");
        };
        let Some(CStmt::Return(Some(zero_expr))) = zero_stmts.last() else {
            panic!("zero block should fold to return, got {zero_stmts:?}");
        };
        assert_eq!(one_expr, &CExpr::IntLit(1));
        assert_eq!(zero_expr, &CExpr::IntLit(0));
    }

    #[test]
    fn folded_x86_solve_equation_fixture_shape_uses_arg_not_raw_stack_deref() {
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                canonical_storage: None,
            },
            PhiNode {
                dst: make_var("tmp:6a80", 5, 4),
                sources: vec![
                    (0x100000868, make_var("tmp:6a80", 0, 4)),
                    (0x100000871, make_var("tmp:6a80", 0, 4)),
                ],
                canonical_storage: None,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                    ctx.name_ref("arg0"),
                    CExpr::IntLit(1),
                ),
                CExpr::IntLit(5),
            ),
            CExpr::IntLit(25),
        );
        let expected_named_local = CExpr::binary(
            BinaryOp::Ne,
            ctx.name_ref("local_c"),
            CExpr::IntLit(25),
        );
        assert!(
            cond == expected_arithmetic || cond == expected_named_local,
            "expected solve_equation predicate to stay scalar and avoid raw stack derefs, got {cond:?}"
        );

        let then_stmts = ctx.fold_block(func.get_block(0x100000868).expect("then"), 0x100000868);
        let else_stmts = ctx.fold_block(func.get_block(0x100000871).expect("else"), 0x100000871);
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

        let mut ctx = make_x86_64_ctx();
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        ctx.analyze_blocks(&fold_blocks);
        ctx.analyze_function_structure(&func);
        let condition = ctx
            .extract_condition_from_block(func.get_block(0x1000).expect("entry"))
            .expect("strcmp condition");

        assert!(
            condition != CExpr::binary(BinaryOp::Ne, CExpr::IntLit(0), CExpr::IntLit(0)),
            "no-calldefine strcmp condition should not collapse to a constant"
        );
    }

    #[test]
    fn folded_x86_bool_carrier_chain_recovers_scalar_condition_and_branch_returns() {
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
                space: r2il::SpaceId::Ram,
                addr: make_var("tmp:condaddr", 1, 8),
                val: make_var("tmp:widen", 1, 4),
            },
            SSAOp::Load {
                dst: make_var("tmp:condreload", 1, 4),
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                ctx.name_ref("arg0"),
                ctx.name_ref("arg1"),
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
        assert_eq!(then_expr, &ctx.name_ref("arg0"));
        assert_eq!(else_expr, &ctx.name_ref("arg1"));
    }

    #[test]
    fn folded_x86_bool_carrier_chain_fixture_shape_recovers_scalar_condition_and_branch_returns() {
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                canonical_storage: None,
            },
            PhiNode {
                dst: make_var("RAX", 6, 8),
                sources: vec![
                    (0x10000107a, make_var("RAX", 0, 8)),
                    (0x100001082, make_var("RAX", 0, 8)),
                ],
                canonical_storage: None,
            },
            PhiNode {
                dst: make_var("tmp:11f00", 5, 4),
                sources: vec![
                    (0x10000107a, make_var("tmp:11f00", 0, 4)),
                    (0x100001082, make_var("tmp:11f00", 0, 4)),
                ],
                canonical_storage: None,
            },
            PhiNode {
                dst: make_var("tmp:4700", 13, 8),
                sources: vec![
                    (0x10000107a, make_var("tmp:4700", 0, 8)),
                    (0x100001082, make_var("tmp:4700", 0, 8)),
                ],
                canonical_storage: None,
            },
            PhiNode {
                dst: make_var("tmp:6a80", 7, 4),
                sources: vec![
                    (0x10000107a, make_var("tmp:6a80", 0, 4)),
                    (0x100001082, make_var("tmp:6a80", 0, 4)),
                ],
                canonical_storage: None,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                space: r2il::SpaceId::Ram,
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
                ctx.name_ref("arg0"),
                ctx.name_ref("arg1"),
            )
        );
        let then_stmts = ctx.fold_block(func.get_block(0x100001082).expect("then"), 0x100001082);
        let else_stmts = ctx.fold_block(func.get_block(0x10000107a).expect("else"), 0x10000107a);
        assert_eq!(
            then_stmts,
            vec![CStmt::Return(Some(ctx.name_ref("arg0")))]
        );
        assert_eq!(
            else_stmts,
            vec![CStmt::Return(Some(ctx.name_ref("arg1")))]
        );
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
            ctx.name_ref("rbp"),
            CExpr::IntLit(-8),
        )));
        let raw_return_stack_load = CExpr::Deref(Box::new(CExpr::binary(
            BinaryOp::Add,
            ctx.name_ref("rbp"),
            CExpr::IntLit(-12),
        )));
        let scalar_arg1 = ctx.name_ref("arg1");
        assert_eq!(
            ctx.debug_choose_scalar_predicate_expr(
                Some(raw_stack_load.clone()),
                Some(scalar_arg1.clone()),
            ),
            Some(scalar_arg1.clone())
        );
        assert_eq!(
            ctx.debug_choose_scalar_predicate_expr(
                Some(CExpr::AddrOf(Box::new(ctx.name_ref("var_8h")))),
                Some(scalar_arg1.clone()),
            ),
            Some(scalar_arg1.clone())
        );

        let scalar_arg2 = ctx.name_ref("arg2");
        assert_eq!(
            ctx.debug_choose_scalar_return_expr(
                Some(CExpr::AddrOf(Box::new(ctx.name_ref("var_ch")))),
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
                Some(ctx.name_ref("arg1")),
                Some(CExpr::AddrOf(Box::new(ctx.name_ref("var_8h")))),
            ),
            Some(CExpr::AddrOf(Box::new(ctx.name_ref("var_8h"))))
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
            ctx.name_ref("var_4h")
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
            },
        );
        let function_names = HashMap::from([(0x401500, "helper.alloc_wrapper".to_string())]);
        let callee_facts = BTreeMap::from([(
            0x401500,
            CalleeFact {
                function_id: 0x401500,
                name: Some("helper.alloc_wrapper".to_string()),
                linkage: r2types::CalleeLinkage::Internal,
                signature: None,
                signature_callconv: None,
                signature_noreturn: false,
                model_policy_evidence: BTreeSet::from([
                    r2types::CalleeModelPolicyEvidence::InterprocSummary,
                ]),
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
        )]);
        let known_signatures = HashMap::new();
        let callee_resolution = r2types::CalleeResolutionFacts::from_direct_call_targets(
            [(
                r2types::CallsiteKey {
                    block_addr: source_call.0,
                    op_index: source_call.1,
                },
                0x401500,
            )],
            &r2types::CalleeIdentityContext {
                function_names: &function_names,
                symbols: ctx.inputs.symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_signatures,
            },
        );
        ctx.inputs.function_names = Box::leak(Box::new(function_names));
        install_function_callee_facts(&mut ctx, callee_facts);
        mutate_function_facts(&mut ctx, |function_facts| {
            function_facts.set_callee_resolution(callee_resolution);
        });

        let rendered = ctx.render_call_args_for_site(
            source_call.0,
            source_call.1,
            &ctx.name_ref("helper.alloc_wrapper"),
            vec![result_call_arg(
                ctx.name_ref("tmp:buf"),
                source_call,
                0,
            )],
        );

        assert_eq!(
            rendered,
            vec![ctx.name_ref("buf")],
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
        let function_names = HashMap::from([(0x401050, "sym.function_name".to_string())]);
        let symbols = HashMap::from([(0x401050, "sym.symbol_name".to_string())]);
        let callee_facts = BTreeMap::from([(
            0x401050,
            minimal_import_callee_fact(0x401050, "sym.imp.fact_helper"),
        )]);
        let known_signatures = HashMap::new();
        let callee_resolution = r2types::CalleeResolutionFacts::from_direct_call_targets(
            [(
                r2types::CallsiteKey {
                    block_addr: 0x1000,
                    op_index: 1,
                },
                0x401050,
            )],
            &r2types::CalleeIdentityContext {
                function_names: &function_names,
                symbols: &symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_signatures,
            },
        );
        ctx.inputs.function_names = Box::leak(Box::new(function_names));
        ctx.inputs.symbols = Box::leak(Box::new(symbols));
        install_function_callee_facts(&mut ctx, callee_facts);
        mutate_function_facts(&mut ctx, |function_facts| {
            function_facts.set_callee_resolution(callee_resolution);
        });

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
        assert_eq!(
            identity.display_name.as_deref(),
            Some("sym.imp.fact_helper")
        );
        assert_eq!(identity.primary_key(), "fact_helper");
        assert!(identity.aliases.contains("sym.function_name"));
        assert!(identity.aliases.contains("sym.symbol_name"));

        assert_eq!(
            ctx.resolve_call_target_for_site(block.addr, 1, target),
            ctx.name_ref("sym.imp.fact_helper")
        );
        assert_eq!(
            ctx.call_target_identity(&ctx.name_ref("const:401050")),
            Some("fact_helper".to_string())
        );
        assert!(
            ctx.is_imported_call_target(&ctx.name_ref("const:401050")),
            "direct target identity should classify imported callee-fact names"
        );
        assert!(
            !ctx.is_modeled_call_target(&ctx.name_ref("const:402000")),
            "unrelated direct targets must not inherit modeled status from existing callee facts"
        );
    }

    #[test]
    fn prepared_direct_call_target_uses_function_facts_copied_const_target() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });

        let prepared =
            prepared_from_r2il_blocks(&[entry], &arch).with_name("prepared_direct_copied_target");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_certified_function_facts(&mut ctx);

        assert_eq!(
            ctx.prepared_direct_call_target(0x1000, 1),
            Some(0x401050),
            "prepared direct targets must come through FunctionFacts callsite evidence"
        );
    }

    #[test]
    fn prepared_direct_call_target_requires_function_facts_direct_target() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });

        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("prepared_direct_copied_target_without_fact");
        let mut callsite_facts = test_callsite_facts(&prepared);
        callsite_facts
            .by_callsite
            .get_mut(&r2types::CallsiteKey {
                block_addr: 0x1000,
                op_index: 1,
            })
            .expect("fixture callsite facts")
            .direct_target = None;

        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_ssa = Some(&prepared);
        install_function_callsite_facts(&mut ctx, callsite_facts);

        assert_eq!(
            ctx.prepared_direct_call_target(0x1000, 1),
            None,
            "r2dec must not reparse copied constants when FunctionFacts omits direct-target evidence"
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
        install_certified_function_facts(&mut ctx);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        install_callsite_resolution(&mut ctx, (0x1000, 2), 0x401050, "sym.helper", None);

        let block = prepared.function().get_block(0x1000).expect("entry");
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[2], block.addr, 2)
            .expect("call stmt");

        let CStmt::Expr(CExpr::Call { func, args }) = stmt else {
            panic!("expected certified call expression, got {stmt:?}");
        };
        assert_eq!(*func, ctx.name_ref("sym.helper"));
        assert_eq!(args, vec![CExpr::IntLit(7)]);
    }

    #[test]
    fn certified_call_args_reject_local_raw_args_without_function_facts_contract() {
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
            .with_name("certified_raw_call_arg_without_facts");
        let call_cert = prepared
            .callsite_certificate_for_op(0x1000, 2)
            .expect("callsite certificate");
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_ssa = Some(&prepared);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        install_callsite_resolution(&mut ctx, (0x1000, 2), 0x401050, "sym.helper", None);
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 2),
            vec![
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::FallbackExpr(CExpr::IntLit(7)),
                )
                .with_source_call(0x1000, 2)
                .with_source_value_id(call_cert.argument_values[0]),
            ],
        );

        let block = prepared.function().get_block(0x1000).expect("entry");
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[2], block.addr, 2)
            .expect("residual stmt");

        assert!(
            matches!(&stmt, CStmt::Comment(comment) if comment.contains("uncertified callsite arguments")),
            "local raw call args with matching SSA value ids must not bypass FunctionFacts callsite facts, got {stmt:?}"
        );
    }

    #[test]
    fn certified_call_args_ignore_prepared_value_mismatch() {
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

        let prepared = prepared_from_r2il_blocks(&[entry], &arch).with_name("mismatched_call_arg");
        let call_cert = prepared
            .callsite_certificate_for_op(0x1000, 2)
            .expect("callsite certificate");
        assert_ne!(
            call_cert.target, call_cert.argument_values[0],
            "target value should be a distinct wrong argument proof"
        );

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_certified_function_facts(&mut ctx);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 2),
                crate::analysis::PreparedCallView {
                    direct_target: Some(0x401050),
                    callee_identity: Some(r2types::CalleeIdentity::from_name("sym.helper")),
                    authoritative_args: vec![CExpr::IntLit(7)],
                    authoritative_arg_values: vec![call_cert.target],
                    result_owner: None,
                    render_fact: None,
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        let block = prepared.function().get_block(0x1000).expect("entry");
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[2], block.addr, 2)
            .expect("certified call stmt");

        let CStmt::Expr(CExpr::Call { func, args }) = stmt else {
            panic!("expected certified call expression, got {stmt:?}");
        };
        assert_eq!(*func, ctx.name_ref("sym.helper"));
        assert_eq!(
            args,
            vec![CExpr::IntLit(7)],
            "prepared arg value mismatch must not override FunctionFacts argument values"
        );
        assert_eq!(
            ctx.render_authoritative_source_args_for_call((0x1000, 2)),
            vec![CExpr::IntLit(7)],
            "source-call replay must also ignore stale PreparedSemanticView argument values"
        );
    }

    #[test]
    fn synthesized_source_call_expr_ignores_prepared_argument_values() {
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
        install_certified_function_facts(&mut ctx);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 2),
                crate::analysis::PreparedCallView {
                    direct_target: Some(0x401050),
                    callee_identity: Some(r2types::CalleeIdentity::from_name("sym.helper")),
                    authoritative_args: vec![CExpr::IntLit(7)],
                    authoritative_arg_values: vec![call_cert.target],
                    result_owner: None,
                    render_fact: None,
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        assert_eq!(
            ctx.synthesized_call_expr_for_source_call((0x1000, 2)),
            Some(CExpr::call(
                ctx.name_ref("sym.helper"),
                vec![CExpr::IntLit(7)]
            )),
            "synthesized source-call expressions must use FunctionFacts argument values, not prepared arg ids"
        );
    }

    #[test]
    fn certified_call_result_owner_alias_requires_certified_stack_identity() {
        let symbols = test_table();
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x10, 8),
            src: Varnode::register(0x00, 8),
        });
        entry.push(R2ILOp::IntSub {
            dst: Varnode::unique(0x500, 8),
            a: Varnode::register(0x28, 8),
            b: Varnode::constant(8, 8),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x500, 8),
            val: Varnode::constant(0, 8),
        });

        let prepared = prepared_x86_with_stack_slot(
            &[entry],
            &arch,
            r2ssa::StackAddressBase::StackPointer,
            -8,
            8,
        )
        .with_name("certified_call_result_stack_alias");
        let source_call = (0x1000, 1);
        let call_results = test_call_result_facts_with_owner_for_source(&prepared, source_call);
        let prepared_view = || PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                source_call,
                crate::analysis::PreparedCallView {
                    direct_target: Some(0x401050),
                    callee_identity: Some(r2types::CalleeIdentity::from_name("sym.helper")),
                    authoritative_args: Vec::new(),
                    authoritative_arg_values: Vec::new(),
                    result_owner: Some(crate::symbol::var_ref(&symbols, "buf")),
                    render_fact: None,
                },
            )]),
            ..PreparedSemanticView::default()
        };

        let mut uncertified_alias_ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_function_call_result_facts(&mut uncertified_alias_ctx, call_results);
        uncertified_alias_ctx.inputs.prepared_semantic_view =
            Some(Box::leak(Box::new(prepared_view())));
        uncertified_alias_ctx
            .state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("alias".to_string(), source_call);
        uncertified_alias_ctx
            .state
            .analysis_ctx
            .use_info
            .insert_semantic_value_for_name(
                "alias",
                crate::analysis::SemanticValue::Address(crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::StackSlot(-8),
                    index: None,
                    scale_bytes: 0,
                    offset_bytes: 0,
                }),
            );

        assert_eq!(
            uncertified_alias_ctx.stable_owned_call_result_name_for_source(source_call),
            Some("buf".to_string()),
            "fixture must have a FunctionFacts-backed prepared owner"
        );
        assert_eq!(
            uncertified_alias_ctx.stable_owned_call_result_expr_for_name("alias", true),
            None,
            "semantic stack-owner aliases must not certify call-result ownership"
        );

        let mut certified_alias_ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_function_call_result_facts(
            &mut certified_alias_ctx,
            test_call_result_facts_with_owner_for_source(&prepared, source_call),
        );
        certified_alias_ctx.inputs.prepared_semantic_view =
            Some(Box::leak(Box::new(prepared_view())));
        certified_alias_ctx.inputs.visible_bindings =
            Box::leak(Box::new(vec![visible_stack_binding(
                "alias",
                Some(CType::Int(32)),
                8,
            )]));
        certified_alias_ctx
            .state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert("alias".to_string(), source_call);
        certified_alias_ctx
            .state
            .analysis_ctx
            .use_info
            .insert_stack_slot_for_name("alias", StackSlotProvenance::new(-8));

        assert_eq!(
            certified_alias_ctx.stable_owned_call_result_expr_for_name("alias", true),
            Some(crate::symbol::var_ref(&symbols, "buf")),
            "exact typed/render stack alias evidence should allow the prepared call-result owner"
        );
    }

    #[test]
    fn certified_zero_arg_call_ignores_prepared_fake_args() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Call {
            target: Varnode::constant(0x401050, 8),
        });

        let prepared = prepared_from_r2il_blocks(&[entry], &arch).with_name("uncertified_call_arg");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        install_callsite_resolution(&mut ctx, (0x1000, 0), 0x401050, "sym.helper", None);
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 0),
                crate::analysis::PreparedCallView {
                    authoritative_args: vec![ctx.name_ref("fake_arg")],
                    ..crate::analysis::PreparedCallView::default()
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        let block = prepared.function().get_block(0x1000).expect("entry");
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[0], block.addr, 0)
            .expect("certified call stmt");

        let CStmt::Expr(CExpr::Call { func, args }) = stmt else {
            panic!("expected certified zero-arg call, got {stmt:?}");
        };
        assert_eq!(*func, ctx.name_ref("sym.helper"));
        assert!(
            args.is_empty(),
            "prepared fake args must not override a zero-arg FunctionFacts callsite"
        );
    }

    #[test]
    fn unprepared_call_args_residualize_instead_of_replaying_analyzed_args() {
        let mut ctx = make_x86_64_ctx();
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![crate::analysis::CallArgBinding::input(
                crate::analysis::SemanticCallArg::FallbackExpr(ctx.name_ref("fake_arg")),
            )],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401050", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("residual stmt");

        let CStmt::Comment(comment) = stmt else {
            panic!("expected residual comment for unprepared call args, got {stmt:?}");
        };
        assert!(
            comment.contains("uncertified callsite arguments"),
            "unprepared analyzer call args must not render as executable C: {comment}"
        );
    }

    #[test]
    fn unprepared_call_args_with_fake_source_name_residualize() {
        let mut ctx = make_x86_64_ctx();
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        let mut fake_binding = crate::analysis::CallArgBinding::input(
            crate::analysis::SemanticCallArg::FallbackExpr(ctx.name_ref("fake_arg")),
        );
        fake_binding.source_var_name = Some("__test_source".to_string());
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((0x1000, 0), vec![fake_binding]);

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401050", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("residual stmt");

        let CStmt::Comment(comment) = stmt else {
            panic!("expected residual comment for fake source name, got {stmt:?}");
        };
        assert!(
            comment.contains("uncertified callsite arguments"),
            "bare source names without prepared evidence must not authorize rendering: {comment}"
        );
    }

    #[test]
    fn unprepared_call_args_with_source_call_residualize() {
        let mut ctx = make_x86_64_ctx();
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::FallbackExpr(CExpr::Var(
                        { let CExpr::Var(id) = ctx.name_ref("fake_arg") else { unreachable!() }; id },
                    )),
                )
                .with_source_call(0x1000, 0),
            ],
        );

        let stmt = ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401050", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("residual stmt");

        let CStmt::Comment(comment) = stmt else {
            panic!("expected residual comment for source-call-only args, got {stmt:?}");
        };
        assert!(
            comment.contains("uncertified callsite arguments"),
            "source_call proves provenance, not call-argument render authority: {comment}"
        );
    }

    #[test]
    fn non_certified_call_args_require_function_render_facts() {
        let callsite = r2types::CallsiteKey {
            block_addr: 0x1000,
            op_index: 0,
        };
        let arg_value = r2ssa::ValueId(11);
        let callsite_facts = || r2types::FunctionCallsiteFacts {
            by_callsite: BTreeMap::from([(
                callsite,
                r2types::CallsiteArgumentFacts {
                    callsite,
                    call_site_id: r2ssa::CallSiteId(1),
                    at: r2ssa::InstId(2),
                    target: r2ssa::ValueId(10),
                    direct_target: Some(0x401050),
                    argument_values: vec![r2types::CallArgumentValueFact {
                        index: 0,
                        value: arg_value,
                    }],
                    register_argument_locations: vec![r2types::RegisterCallArgumentLocationFact {
                        index: 0,
                        value: arg_value,
                        name: "rdi".to_string(),
                        source_inst: Some(r2ssa::InstId(1)),
                    }],
                    stack_argument_locations: Vec::new(),
                },
            )]),
        };

        let mut source_name_ctx = make_x86_64_ctx();
        install_function_callsite_facts(&mut source_name_ctx, callsite_facts());
        source_name_ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        install_callsite_resolution(
            &mut source_name_ctx,
            (0x1000, 0),
            0x401050,
            "sym.helper",
            None,
        );
        let mut source_name_binding = crate::analysis::CallArgBinding::input(
            crate::analysis::SemanticCallArg::FallbackExpr(CExpr::IntLit(7)),
        );
        source_name_binding.source_var_name = Some("__test_source".to_string());
        source_name_ctx
            .state
            .analysis_ctx
            .use_info
            .call_args
            .insert((0x1000, 0), vec![source_name_binding]);
        let source_name_stmt = source_name_ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401050", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("residual stmt");
        assert!(
            matches!(&source_name_stmt, CStmt::Comment(comment) if comment.contains("uncertified callsite arguments")),
            "source names must not authorize executable call args without a FunctionFacts value match: {source_name_stmt:?}"
        );

        let mut value_ctx = make_x86_64_ctx();
        install_function_callsite_facts(&mut value_ctx, callsite_facts());
        value_ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        install_callsite_resolution(&mut value_ctx, (0x1000, 0), 0x401050, "sym.helper", None);
        value_ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 0),
            vec![
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::FallbackExpr(CExpr::IntLit(7)),
                )
                .with_source_value_id(arg_value),
            ],
        );
        let value_stmt = value_ctx
            .op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("const:401050", 0, 8),
                },
                0x1000,
                0,
            )
            .expect("residual stmt");
        assert!(
            matches!(&value_stmt, CStmt::Comment(comment) if comment.contains("uncertified callsite arguments")),
            "raw value-id matches must not authorize executable call args without FunctionRenderFacts: {value_stmt:?}"
        );
    }

    #[test]
    fn certified_call_arg_uses_function_facts_value_over_unknown_semantic_binding() {
        let symbols = test_table();
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
            prepared_from_r2il_blocks(&[entry], &arch).with_name("unknown_semantic_call_arg");
        let call_cert = prepared
            .callsite_certificate_for_op(0x1000, 2)
            .expect("callsite certificate");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        install_callsite_resolution(&mut ctx, (0x1000, 2), 0x401050, "sym.helper", None);
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 2),
                crate::analysis::PreparedCallView {
                    direct_target: Some(0x401050),
                    callee_identity: Some(r2types::CalleeIdentity::from_name("sym.helper")),
                    authoritative_args: Vec::new(),
                    authoritative_arg_values: Vec::new(),
                    result_owner: None,
                    render_fact: None,
                },
            )]),
            ..PreparedSemanticView::default()
        })));
        install_certified_function_facts(&mut ctx);
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 2),
            vec![
                crate::analysis::CallArgBinding::input(crate::analysis::SemanticCallArg::semantic(
                    crate::analysis::SemanticValue::Unknown,
                ))
                .with_source_call(0x1000, 2)
                .with_source_value_id(call_cert.argument_values[0]),
            ],
        );

        let block = prepared.function().get_block(0x1000).expect("entry");
        let rendered_args = ctx.render_call_args_for_site_with_direct_target(
            block.addr,
            2,
            &ctx.name_ref("sym.helper"),
            Some(0x401050),
            ctx.call_args_map()
                .get(&(0x1000, 2))
                .cloned()
                .expect("raw args"),
        );
        assert_eq!(
            rendered_args,
            vec![ctx.unresolved_call_arg_expr()],
            "unknown semantic args must stay visibly unresolved before certification"
        );

        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[2], block.addr, 2)
            .expect("certified call stmt");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected certified call expression, got {stmt:?}");
        };
        assert_eq!(
            args,
            vec![CExpr::IntLit(7)],
            "FunctionFacts argument value proof must override stale unknown raw semantic binding"
        );
    }

    #[test]
    fn certified_prepared_string_arg_rejects_poisoned_render_text() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x10, 8),
            src: Varnode::constant(0x402000, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });

        let prepared =
            prepared_from_r2il_blocks(&[entry], &arch).with_name("poisoned_prepared_string_arg");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_certified_function_facts(&mut ctx);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        install_callsite_resolution(&mut ctx, (0x1000, 2), 0x401050, "sym.helper", None);
        let call_cert = prepared
            .callsite_certificate_for_op(0x1000, 2)
            .expect("callsite certificate");
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 2),
                crate::analysis::PreparedCallView {
                    direct_target: Some(0x401050),
                    callee_identity: Some(r2types::CalleeIdentity::from_name("sym.helper")),
                    authoritative_args: vec![CExpr::StringLit("poison".to_string())],
                    authoritative_arg_values: vec![call_cert.argument_values[0]],
                    result_owner: None,
                    render_fact: None,
                },
            )]),
            ..PreparedSemanticView::default()
        })));

        let block = prepared.function().get_block(0x1000).expect("entry");
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[2], block.addr, 2)
            .expect("certified call stmt");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!(
                "expected certified call expression for poisoned prepared string arg, got {stmt:?}"
            );
        };
        assert_eq!(
            args,
            vec![CExpr::IntLit(0x402000)],
            "prepared string text must be ignored without exact source-owned string evidence"
        );
    }

    #[test]
    fn certified_string_addr_call_arg_mismatch_uses_function_facts_value() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x10, 8),
            src: Varnode::constant(0x402000, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });

        let prepared =
            prepared_from_r2il_blocks(&[entry], &arch).with_name("mismatched_string_addr_call_arg");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_certified_function_facts(&mut ctx);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        ctx.inputs.strings = Box::leak(Box::new(HashMap::from([(0x403000, "wrong".to_string())])));
        install_callsite_resolution(&mut ctx, (0x1000, 2), 0x401050, "sym.helper", None);
        ctx.inputs.prepared_semantic_view =
            Some(Box::leak(Box::new(PreparedSemanticView::default())));
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 2),
            vec![
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::StringAddr(0x403000),
                )
                .with_source_call(0x1000, 2),
            ],
        );

        let block = prepared.function().get_block(0x1000).expect("entry");
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[2], block.addr, 2)
            .expect("certified call stmt");

        let CStmt::Expr(CExpr::Call { args, .. }) = stmt else {
            panic!("expected certified call expression, got {stmt:?}");
        };
        assert_eq!(
            args,
            vec![CExpr::IntLit(0x402000)],
            "FunctionFacts value address must override stale raw string binding"
        );
    }

    #[test]
    fn certified_noncarrier_phis_remain_semantic_expressions() {
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
        let render_facts = test_render_facts(&prepared);
        let normalized = crate::normalize::materialize_certified_loop_carriers(
            prepared.function(),
            &prepared,
            &render_facts,
        );
        assert!(
            normalized
                .get_block(0x181c)
                .is_some_and(|block| !block.phis.is_empty()),
            "ordinary merge phis must remain immutable certified expressions"
        );
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
            "noncarrier phi predecessors should not invent mutable render effects: {rendered:?}"
        );
    }

    #[test]
    fn certified_materialized_memory_result_is_not_inlined() {
        let arch = make_test_arch_x86_64();
        let mut block = R2ILBlock::new(0x2000, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: r2il::SpaceId::Ram,
            addr: Varnode::register(0x10, 8),
        });
        block.push(R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: Varnode::register(0x18, 8),
            val: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: Varnode::register(0x18, 8),
            val: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[block], &arch);
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_certified_function_facts(&mut ctx);
        let blocks = prepared.function().blocks().cloned().collect::<Vec<_>>();
        ctx.analyze_blocks(&blocks);
        let fact = ctx
            .inputs
            .function_facts
            .render_facts()
            .memory_accesses()
            .find(|fact| !fact.is_write)
            .expect("certified load");
        assert!(fact.materialize_result);
        let value = fact.value.expect("load result");
        let var = prepared.value_var(value).expect("prepared load result");

        assert!(
            !ctx.should_inline(var),
            "certified memory result {} must remain a single evaluated assignment",
            crate::certified_memory_result_name(fact.access)
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
                ctx.name_ref("arg0"),
                CExpr::IntLit(0),
            ))
        );
        assert_eq!(
            ctx.predicate_candidate_for_var(cond),
            Some(CExpr::binary(
                BinaryOp::Ne,
                ctx.name_ref("arg0"),
                CExpr::IntLit(0),
            ))
        );
    }

    #[test]
    fn prepared_predicate_alias_cycle_returns_stable_var_instead_of_recursing() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            owner_expr_by_name: HashMap::from([
                (
                    "tmp:pred.1".to_string(),
                    ctx.name_ref("tmp:pred.2"),
                ),
                (
                    "tmp:pred.2".to_string(),
                    ctx.name_ref("tmp:pred.1"),
                ),
            ]),
            ..PreparedSemanticView::default()
        })));

        let mut visited = HashSet::new();
        let resolved =
            ctx.resolve_predicate_operand(&ctx.name_ref("tmp:pred.1"), 0, &mut visited);

        assert_eq!(resolved, ctx.name_ref("tmp:pred.1"));
    }

    #[test]
    fn prepared_empty_call_view_args_do_not_replay_analyzed_call_args() {
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
                crate::analysis::SemanticCallArg::FallbackExpr(ctx.name_ref("len")),
            )],
        );

        assert_eq!(
            ctx.render_authoritative_source_args_for_call((0x1000, 1)),
            Vec::<CExpr>::new(),
            "empty prepared call facts must not authorize raw analyzed arg replay"
        );
    }

    #[test]
    fn certified_source_call_replay_requires_function_facts_callsite_args() {
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
            .with_name("certified_source_call_no_functionfacts_args");
        let call_cert = prepared
            .callsite_certificate_for_op(0x1000, 2)
            .expect("prepared callsite certificate");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        remove_function_callsite_facts(&mut ctx);
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 2),
                crate::analysis::PreparedCallView {
                    direct_target: Some(0x401050),
                    callee_identity: Some(r2types::CalleeIdentity::from_name("sym.helper")),
                    authoritative_args: vec![CExpr::IntLit(99)],
                    authoritative_arg_values: vec![call_cert.argument_values[0]],
                    result_owner: None,
                    render_fact: None,
                },
            )]),
            ..PreparedSemanticView::default()
        })));
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 2),
            vec![
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::FallbackExpr(CExpr::IntLit(88)),
                )
                .with_source_value_id(call_cert.argument_values[0]),
            ],
        );

        assert_eq!(
            ctx.render_authoritative_source_args_for_call((0x1000, 2)),
            Vec::<CExpr>::new(),
            "certified source-call replay must not use PreparedSemanticView or local call_args_map without FunctionFacts callsite args"
        );
    }

    #[test]
    fn certified_source_call_replay_requires_function_render_arg_proof() {
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
            .with_name("certified_source_call_no_render_arg_proof");
        let call_cert = prepared
            .callsite_certificate_for_op(0x1000, 2)
            .expect("prepared callsite certificate");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        remove_function_render_facts(&mut ctx);
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 2),
                crate::analysis::PreparedCallView {
                    direct_target: Some(0x401050),
                    callee_identity: Some(r2types::CalleeIdentity::from_name("sym.helper")),
                    authoritative_args: vec![CExpr::IntLit(99)],
                    authoritative_arg_values: vec![call_cert.argument_values[0]],
                    result_owner: None,
                    render_fact: None,
                },
            )]),
            ..PreparedSemanticView::default()
        })));
        ctx.state.analysis_ctx.use_info.call_args.insert(
            (0x1000, 2),
            vec![
                crate::analysis::CallArgBinding::input(
                    crate::analysis::SemanticCallArg::FallbackExpr(CExpr::IntLit(88)),
                )
                .with_source_value_id(call_cert.argument_values[0]),
            ],
        );

        assert_eq!(
            ctx.render_authoritative_source_args_for_call((0x1000, 2)),
            Vec::<CExpr>::new(),
            "certified source-call replay must not use PreparedSemanticView or local call_args_map when FunctionRenderFacts cannot render the canonical argument value"
        );
    }

    #[test]
    fn certified_render_plan_requires_renderable_exact_nonraw_call_arg() {
        let symbols = test_table();
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
            prepared_from_r2il_blocks(&[entry], &arch).with_name("certified_prepared_view_arg");
        let arg_value = prepared
            .callsite_certificate_for_op(0x1000, 2)
            .expect("prepared callsite certificate")
            .argument_values[0];
        let render_facts = |renderable| {
            let id = r2ssa::SemanticId::expression(arg_value);
            r2types::FunctionRenderFacts {
                certified_exprs: BTreeMap::from([(
                    id,
                    r2types::CertifiedExpr {
                        id,
                        fact: r2types::ExpressionRenderFact {
                            value: arg_value,
                            defining_inst: None,
                            width: 8,
                            renderable,
                        },
                        inputs: Vec::new(),
                        bindings: BTreeSet::new(),
                        guarded_phi: None,
                    },
                )]),
                ..r2types::FunctionRenderFacts::default()
            }
        };
        let prepared_view = |value, expr| PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                (0x1000, 2),
                crate::analysis::PreparedCallView {
                    authoritative_args: vec![expr],
                    authoritative_arg_values: vec![value],
                    render_fact: Some(r2types::CallsiteRenderFact {
                        callsite: r2types::CallsiteKey {
                            block_addr: 0x1000,
                            op_index: 2,
                        },
                        target: None,
                        disposition: r2types::CallsiteRenderDisposition::SideEffectStatement,
                        proof_values: vec![value],
                        residual_reason: None,
                    }),
                    ..crate::analysis::PreparedCallView::default()
                },
            )]),
            ..PreparedSemanticView::default()
        };

        let render = render_facts(true);
        let view = prepared_view(arg_value, crate::symbol::var_ref(&symbols, "n"));
        let function_facts = r2types::FunctionFacts::default();
        let adapter = CertifiedRenderPlan::new(&symbols, 
            &function_facts,
            &view,
            CertifiedRenderContext::new(&prepared, &render),
        );
        assert_eq!(
            adapter.call_arg_expr((0x1000, 2), arg_value, |_| false),
            Some(crate::symbol::var_ref(&symbols, "n"))
        );

        let unrenderable = render_facts(false);
        let adapter = CertifiedRenderPlan::new(&symbols, 
            &function_facts,
            &view,
            CertifiedRenderContext::new(&prepared, &unrenderable),
        );
        assert_eq!(
            adapter.call_arg_expr((0x1000, 2), arg_value, |_| false),
            None
        );

        let wrong_value_view = prepared_view(r2ssa::ValueId(9999), crate::symbol::var_ref(&symbols, "n"));
        let adapter = CertifiedRenderPlan::new(&symbols, 
            &function_facts,
            &wrong_value_view,
            CertifiedRenderContext::new(&prepared, &render),
        );
        assert_eq!(
            adapter.call_arg_expr((0x1000, 2), arg_value, |_| false),
            None
        );

        let raw_storage_view = prepared_view(arg_value, crate::symbol::var_ref(&symbols, "tmp:raw_1"));
        let adapter = CertifiedRenderPlan::new(&symbols, 
            &function_facts,
            &raw_storage_view,
            CertifiedRenderContext::new(&prepared, &render),
        );
        assert_eq!(
            adapter.call_arg_expr((0x1000, 2), arg_value, |_| true),
            None
        );
    }

    #[test]
    fn return_inline_ssa_storage_carriers_inline_raw_tmp_and_const() {
        let mut ctx = make_x86_64_ctx();
        ctx.state.analysis_ctx.use_info.definitions.insert(
            "tmp:ret_1".to_string(),
            CExpr::binary(
                BinaryOp::BitXor,
                ctx.name_ref("value"),
                CExpr::IntLit(1),
            ),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert("const:1_0".to_string(), CExpr::IntLit(1));

        assert_eq!(
            ctx.resolve_return_candidate(&ctx.name_ref("tmp:ret_1")),
            CExpr::binary(
                BinaryOp::BitXor,
                ctx.name_ref("value"),
                CExpr::IntLit(1)
            )
        );
        assert_eq!(
            ctx.resolve_return_candidate(&ctx.name_ref("const:1_0")),
            CExpr::IntLit(1)
        );
    }

    #[test]
    fn return_inline_ssa_storage_carriers_require_raw_or_mapped_alias() {
        let symbols = test_table();
        let mut unmapped = make_x86_64_ctx();
        unmapped
            .state
            .analysis_ctx
            .use_info
            .definitions
            .insert("tmp:3e480_1".to_string(), CExpr::IntLit(7));

        assert_eq!(
            unmapped.expand_return_expr(
                &crate::symbol::var_ref(&symbols, "value_3e480"),
                0,
                &mut HashSet::new()
            ),
            crate::symbol::var_ref(&symbols, "value_3e480")
        );
        assert_eq!(
            unmapped.expand_return_expr(&crate::symbol::var_ref(&symbols, "t42_1"), 0, &mut HashSet::new()),
            crate::symbol::var_ref(&symbols, "t42_1")
        );
        unmapped
            .state
            .analysis_ctx
            .use_info
            .definitions
            .insert("ordinary_alias".to_string(), CExpr::IntLit(9));
        assert_eq!(
            unmapped.expand_return_expr(
                &crate::symbol::var_ref(&symbols, "ordinary_alias"),
                0,
                &mut HashSet::new()
            ),
            crate::symbol::var_ref(&symbols, "ordinary_alias")
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
                &crate::symbol::var_ref(&symbols, "value_3e480"),
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
                ctx.name_ref("s_home"),
                true,
                false,
                false,
            ),
            ctx.name_ref("s")
        );
    }

    #[test]
    fn imported_result_binding_filters_stack_like_call_result_owners() {
        for owner in ["local_buf", "stack_slot", "arg_slot", "arg1", "named_slot"] {
            let mut ctx = make_x86_64_ctx();
            if owner == "named_slot" {
                ctx.state
                    .analysis_ctx
                    .stack_info
                    .stack_vars
                    .insert(-32, owner.to_string());
            }
            install_call_owner(&mut ctx, (0x1000, 0), owner, "rax_1");

            let rendered = ctx.render_call_arg_for_callee(
                &ctx.name_ref("sym.imp.printf"),
                crate::analysis::CallArgBinding::result(
                    crate::analysis::SemanticCallArg::FallbackExpr(CExpr::Var(
                        { let CExpr::Var(id) = ctx.name_ref("fallback") else { unreachable!() }; id },
                    )),
                )
                .with_source_call(0x1000, 0),
            );

            assert_eq!(
                rendered,
                ctx.name_ref("fallback"),
                "{owner} must not bypass the result-call-argument owner filter"
            );
        }
    }

    #[test]
    fn imported_input_binding_with_source_call_does_not_render_result_owner() {
        let mut ctx = make_x86_64_ctx();
        install_call_owner(&mut ctx, (0x1000, 0), "owned_result", "rax_1");

        let rendered = ctx.render_call_arg_for_callee(
            &ctx.name_ref("sym.imp.printf"),
            crate::analysis::CallArgBinding::input(crate::analysis::SemanticCallArg::FallbackExpr(
                ctx.name_ref("input_arg"),
            ))
            .with_source_call(0x1000, 0),
        );

        assert_eq!(rendered, ctx.name_ref("input_arg"));
    }

    #[test]
    fn recovered_call_arg_rejects_low_quality_raw_definition() {
        let mut ctx = make_x86_64_ctx();
        let source = make_var("tmp:src", 1, 8);
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert(source.display_name(), ctx.name_ref("stack_slot"));

        let binding = crate::analysis::CallArgBinding::input(
            crate::analysis::SemanticCallArg::FallbackExpr(ctx.name_ref("fallback")),
        )
        .with_source_var(&source);

        let rendered =
            ctx.render_call_arg_for_callee(&ctx.name_ref("sym.imp.printf"), binding);

        assert_eq!(rendered, ctx.name_ref("fallback"));
    }

    fn install_prepared_owner_for_name(ctx: &mut FoldingContext<'_>, name: &str, owner: CExpr) {
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            owner_expr_by_name: HashMap::from([(name.to_string(), owner)]),
            ..PreparedSemanticView::default()
        })));
    }

    #[test]
    fn recovered_call_arg_rejects_low_signal_sources_without_better_proof() {
        let cases = [
            ("src_transient", ctx.name_ref("rax_7")),
            ("src_stack_placeholder", ctx.name_ref("stack")),
            ("src_low_quality", ctx.name_ref("value_bad")),
        ];

        for (source_name, bad_expr) in cases {
            let mut ctx = make_x86_64_ctx();
            let source = make_var(source_name, 1, 8);
            ctx.state
                .analysis_ctx
                .use_info
                .definitions
                .insert(source.display_name(), bad_expr);

            let binding = crate::analysis::CallArgBinding::input(
                crate::analysis::SemanticCallArg::FallbackExpr(ctx.name_ref("fallback")),
            )
            .with_source_var(&source);

            assert_eq!(
                ctx.render_call_arg_for_callee(&ctx.name_ref("sym.imp.printf"), binding),
                ctx.name_ref("fallback"),
                "{source_name} should not be accepted as recovered imported call arg proof"
            );
        }
    }

    #[test]
    fn recovered_call_arg_contract_rejects_low_signal_sources_directly() {
        let cases = [
            ("src_transient", ctx.name_ref("rax_7")),
            ("src_stack_placeholder", ctx.name_ref("stack")),
            ("src_low_quality", ctx.name_ref("value_bad")),
        ];

        for (source_name, bad_expr) in cases {
            let mut ctx = make_x86_64_ctx();
            let source = make_var(source_name, 1, 8);
            ctx.state
                .analysis_ctx
                .use_info
                .definitions
                .insert(source.display_name(), bad_expr);
            let binding = crate::analysis::CallArgBinding::input(
                crate::analysis::SemanticCallArg::FallbackExpr(ctx.name_ref("fallback")),
            )
            .with_source_var(&source);

            assert_eq!(
                ctx.recover_call_arg_expr_from_source_var(&binding),
                None,
                "{source_name} must not be accepted by the recovered imported-arg contract"
            );
        }
    }

    #[test]
    fn prepared_addr_of_owner_is_not_imported_arg_value() {
        let mut ctx = make_x86_64_ctx();
        let source = make_var("src_addr_owner", 1, 8);
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert(source.display_name(), ctx.name_ref("rax_7"));
        let __fixture_args = (
            &source.display_name(),
            CExpr::AddrOf(Box::new(ctx.name_ref("buf"))),
        );
        install_prepared_owner_for_name(
            &mut ctx,
            __fixture_args.0,
            __fixture_args.1,
        );;

        let binding = crate::analysis::CallArgBinding::input(
            crate::analysis::SemanticCallArg::FallbackExpr(ctx.name_ref("fallback")),
        )
        .with_source_var(&source);

        assert_eq!(
            ctx.render_call_arg_for_callee(&ctx.name_ref("sym.imp.printf"), binding),
            ctx.name_ref("fallback"),
            "prepared address owners describe storage identity, not imported argument values"
        );
    }

    #[test]
    fn recovered_input_arg_contract_preserves_stable_source_over_call_candidate() {
        let mut ctx = make_x86_64_ctx();
        let source = make_var("src_input_call", 1, 8);
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert(source.display_name(), ctx.name_ref("buf"));
        ctx.state.analysis_ctx.use_info.formatted_defs.insert(
            source.display_name(),
            CExpr::call(ctx.name_ref("sym.imp.helper"), vec![]),
        );

        let input_binding = crate::analysis::CallArgBinding::input(
            crate::analysis::SemanticCallArg::FallbackExpr(ctx.name_ref("fallback")),
        )
        .with_source_var(&source);
        assert_eq!(
            ctx.recover_call_arg_expr_from_source_var(&input_binding),
            Some(ctx.name_ref("buf")),
            "input-role recovery must preserve stable source expressions over call candidates"
        );
    }

    #[test]
    fn recovered_input_arg_contract_preserves_wrapped_stable_source_over_entry_alias() {
        let mut ctx = make_x86_64_ctx();
        let source = make_var("src_wrapped_input", 1, 8);
        let stable_source = CExpr::Paren(Box::new(ctx.name_ref("buf")));
        ctx.state
            .analysis_ctx
            .use_info
            .definitions
            .insert(source.display_name(), stable_source.clone());
        ctx.state
            .analysis_ctx
            .use_info
            .formatted_defs
            .insert(source.display_name(), ctx.name_ref("arg1"));

        let input_binding = crate::analysis::CallArgBinding::input(
            crate::analysis::SemanticCallArg::FallbackExpr(ctx.name_ref("fallback")),
        )
        .with_source_var(&source);
        assert_eq!(
            ctx.recover_call_arg_expr_from_source_var(&input_binding),
            Some(stable_source),
            "input-role recovery must not replace a stable source with a generic entry alias"
        );
    }

    #[test]
    fn imported_result_binding_accepts_non_stack_call_result_owner() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x1000, 0);
        install_callsite_resolution(&mut ctx, source_call, 0x401030, "sym.imp.printf", None);
        install_call_owner(&mut ctx, source_call, "owned_result", "rax_1");

        let rendered = ctx.render_call_args_for_site(
            source_call.0,
            source_call.1,
            &ctx.name_ref("const:401030"),
            vec![
                crate::analysis::CallArgBinding::result(
                    crate::analysis::SemanticCallArg::FallbackExpr(CExpr::Var(
                        { let CExpr::Var(id) = ctx.name_ref("fallback") else { unreachable!() }; id },
                    )),
                )
                .with_source_call(source_call.0, source_call.1),
            ],
        );

        assert_eq!(rendered, vec![ctx.name_ref("owned_result")]);
    }

    #[test]
    fn prepared_imported_scalar_expr_uses_precomputed_owner_aliases() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            owner_expr_by_name: HashMap::from([(
                "tmp:size_1".to_string(),
                ctx.name_ref("len"),
            )]),
            ..PreparedSemanticView::default()
        })));

        assert_eq!(
            ctx.prepared_imported_semantic_arg_expr(
                &crate::analysis::SemanticValue::Scalar(ScalarValue::Expr(CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("tmp:size_1"),
                    CExpr::IntLit(1),
                ))),
                false,
            ),
            Some(CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("len"),
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
                    ctx.name_ref("var_8h"),
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
                ctx.name_ref("arg1"),
                ctx.name_ref("arg2"),
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
                        ctx.name_ref("var_8h"),
                        ctx.name_ref("var_8h"),
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
                    ctx.name_ref("arg1"),
                    ctx.name_ref("arg1"),
                ),
                CExpr::IntLit(100),
            ))
        );
    }

    #[test]
    fn prepared_memory_load_ignores_raw_symbol_without_typed_global_fact() {
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
        assert!(
            matches!(right.as_ref(), CExpr::Deref(_)),
            "raw symbol map must not authorize prepared global load rendering: {right:?}"
        );
        assert!(
            !format!("{right:?}").contains("obj.global_value"),
            "raw symbol name must not leak into prepared load expression: {right:?}"
        );
    }






    fn install_hash_field_layout(ctx: &mut FoldingContext<'_>) {
        ctx.inputs.param_register_aliases = Box::leak(Box::new(HashMap::from([
            ("RDI".to_string(), "arg0".to_string()),
            ("rdi".to_string(), "arg0".to_string()),
        ])));
        ctx.set_type_hints(HashMap::from([
            (
                "RDI".to_string(),
                CType::ptr(CType::Struct("DemoStruct".to_string())),
            ),
            (
                "rdi".to_string(),
                CType::ptr(CType::Struct("DemoStruct".to_string())),
            ),
            (
                "arg0".to_string(),
                CType::ptr(CType::Struct("DemoStruct".to_string())),
            ),
        ]));
        ctx.inputs.external_type_db = Box::leak(Box::new(ExternalTypeDb {
            structs: [(
                "demostruct".to_string(),
                ExternalStruct {
                    name: "DemoStruct".to_string(),
                    fields: [(
                        8,
                        ExternalField {
                            name: "hash".to_string(),
                            offset: 8,
                            ty: Some("uint64_t".to_string()),
                        },
                    )]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        }));
    }

    #[test]
    fn certified_member_rendering_allows_exact_field_certificate() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(8, 8),
        });
        entry.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        let external_type_db = ExternalTypeDb {
            structs: [(
                "demostruct".to_string(),
                ExternalStruct {
                    name: "DemoStruct".to_string(),
                    fields: [(
                        8,
                        ExternalField {
                            name: "hash".to_string(),
                            offset: 8,
                            ty: Some("uint64_t".to_string()),
                        },
                    )]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..ExternalTypeDb::default()
        };
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("field_with_cert")
            .with_context(r2types::ParsedExternalContext {
                register_params: vec![r2types::ExternalRegisterParamSpec {
                    name: "arg0".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Struct("DemoStruct".to_string()),
                    ))),
                    reg: "RDI".to_string(),
                }],
                external_type_db,
                ..r2types::ParsedExternalContext::default()
            });
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_hash_field_layout(&mut ctx);
        ctx.inputs.field_access_certificates = Box::leak(Box::new(
            prepared
                .function_facts()
                .type_facts()
                .field_access_certificates
                .clone(),
        ));
        ctx.current_block_addr.set(Some(0x1000));
        ctx.current_op_idx.set(Some(1));

        let addr = crate::analysis::NormalizedAddr {
            base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::new(make_var(
                "RDI", 0, 8,
            ))),
            index: None,
            scale_bytes: 0,
            offset_bytes: 8,
        };
        let mut visited = HashSet::new();
        let expr = ctx.render_access_expr_from_addr(&addr, 8, false, 1, &mut visited);

        assert!(
            matches!(expr.as_ref(), Some(CExpr::PtrMember { member, .. } | CExpr::Member { member, .. }) if member == "hash"),
            "exact FieldAccessCertificate plus FunctionRenderFacts member proof should allow certified member rendering: {expr:?}"
        );
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
                ctx.name_ref("arg0"),
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
        let mut control_facts = r2types::FunctionControlFacts::default();
        control_facts.branch_predicates.insert(
            0x5000,
            r2types::BranchPredicateFact {
                id: r2ssa::PredicateId(1),
                block_addr: 0x5000,
                condition: lhs_value_id,
                comparison: Some(r2types::PredicateComparisonFact {
                    kind: r2ssa::CompareKind::Equal,
                    lhs: lhs_value_id,
                    rhs: rhs_value_id,
                }),
                evaluated_comparison: None,
                render_comparison: Some(r2types::PredicateComparisonFact {
                    kind: r2ssa::CompareKind::Equal,
                    lhs: lhs_value_id,
                    rhs: rhs_value_id,
                }),
                true_target: 0x5008,
                false_target: 0x5004,
            },
        );
        control_facts.block_assumptions.insert(
            0x5000,
            vec![r2types::ControlBlockAssumptionFact {
                predecessor: 0x5000,
                predicate: r2ssa::PredicateId(1),
                truth: true,
            }],
        );
        install_function_control_facts(&mut ctx, control_facts);

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

    #[test]
    fn recent_same_family_return_expr_stops_at_call_boundaries() {
        let ctx = make_x86_64_ctx();
        let old_rax = make_var("rax", 1, 8);
        let new_rax = make_var("rax", 2, 8);

        for barrier in [
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
            SSAOp::CallInd {
                target: make_var("tmp:target", 1, 8),
            },
            SSAOp::CallOther {
                output: Some(make_var("rax", 9, 8)),
                userop: 7,
                inputs: Vec::new(),
            },
        ] {
            let block = make_block(vec![
                SSAOp::Copy {
                    dst: old_rax.clone(),
                    src: make_var("const:2a", 0, 8),
                },
                barrier,
                SSAOp::Copy {
                    dst: new_rax.clone(),
                    src: make_var("argc", 0, 8),
                },
            ]);

            assert!(
                ctx.recent_same_family_return_expr_before(&block, 2, &new_rax)
                    .is_none(),
                "recent return value recovery must not cross call-like barriers"
            );
        }
    }

    #[test]
    fn recent_same_family_return_expr_refuses_other_register_families() {
        let ctx = make_x86_64_ctx();
        let rdi = make_var("rdi", 1, 8);
        let rax = make_var("rax", 1, 8);
        let block = make_block(vec![SSAOp::Copy {
            dst: rdi,
            src: make_var("const:2a", 0, 8),
        }]);

        assert!(
            ctx.recent_same_family_return_expr_before(&block, 1, &rax)
                .is_none(),
            "recent return value recovery must be keyed by storage family"
        );
    }

    #[test]
    fn recent_same_family_return_expr_recovers_prior_same_family_value() {
        let ctx = make_x86_64_ctx();
        let old_rax = make_var("rax", 1, 8);
        let new_rax = make_var("rax", 2, 8);
        let block = make_block(vec![
            SSAOp::Copy {
                dst: old_rax,
                src: make_var("const:2a", 0, 8),
            },
            SSAOp::Copy {
                dst: new_rax.clone(),
                src: make_var("argc", 0, 8),
            },
        ]);

        let recovered = ctx.recent_same_family_return_expr_before(&block, 1, &new_rax);
        assert!(
            matches!(recovered, Some(CExpr::IntLit(42) | CExpr::UIntLit(42))),
            "expected prior same-family value recovery, got {recovered:?}"
        );
    }

    #[test]
    fn recent_same_family_return_expr_copy_uses_return_literal_context() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_return_type = Some(Box::leak(Box::new(CType::Int(32))));
        let target = make_var("rax", 2, 8);
        let block = make_block(vec![SSAOp::Copy {
            dst: make_var("eax", 1, 4),
            src: make_var("const:ffffffff", 0, 4),
        }]);

        assert_eq!(
            ctx.recent_same_family_return_expr_before(&block, 1, &target),
            Some(CExpr::IntLit(-1)),
            "Copy recovery must use return-context literal rewriting"
        );
    }

    #[test]
    fn recent_same_family_return_expr_cast_preserves_declared_narrow_return() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.function_return_type = Some(Box::leak(Box::new(CType::Int(32))));
        let target = make_var("rax", 3, 8);
        let block = make_block(vec![SSAOp::IntZExt {
            dst: make_var("rax", 2, 8),
            src: make_var("const:ffffffff", 0, 4),
        }]);

        assert_eq!(
            ctx.recent_same_family_return_expr_before(&block, 1, &target),
            Some(CExpr::IntLit(-1)),
            "cast-like recovery must preserve declared narrow return expressions"
        );
    }

    #[test]
    fn recent_same_family_return_expr_filters_return_artifacts() {
        let ctx = make_x86_64_ctx();
        let target = make_var("rax", 2, 8);
        for src in [
            make_var("rax", 0, 8),
            make_var("rbp", 0, 8),
            make_var("tmp:dead", 1, 8),
        ] {
            let block = make_block(vec![SSAOp::Copy {
                dst: make_var("rax", 1, 8),
                src,
            }]);
            assert!(
                ctx.recent_same_family_return_expr_before(&block, 1, &target)
                    .is_none(),
                "recent return recovery must not surface transient return artifacts"
            );
        }

        let stack_load = make_block(vec![SSAOp::Load {
            dst: make_var("rax", 1, 8),
            space: r2il::SpaceId::Ram,
            addr: make_var("rbp", 0, 8),
        }]);
        assert!(
            ctx.recent_same_family_return_expr_before(&stack_load, 1, &target)
                .is_none(),
            "recent return recovery must not surface low-level stack dereference artifacts"
        );
    }

    #[test]
    fn local_post_call_source_uses_nearest_call_before_calldefine() {
        let ctx = make_x86_64_ctx();
        let copied = make_var("tmp:out", 1, 8);
        let rax_second = make_var("rax", 2, 8);
        let block = make_block(vec![
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
            SSAOp::CallDefine {
                dst: make_var("rax", 1, 8),
            },
            SSAOp::Call {
                target: make_var("ram:402000", 0, 8),
            },
            SSAOp::CallDefine {
                dst: rax_second.clone(),
            },
            SSAOp::Copy {
                dst: copied.clone(),
                src: rax_second,
            },
        ]);

        assert_eq!(
            ctx.local_post_call_source_for_ssa_name_in_block(&block, &copied.display_name(), 0),
            Some((block.addr, 2)),
            "copied post-call values must resolve to the nearest producing call"
        );
    }

    #[test]
    fn local_post_call_source_follows_copy_like_chain() {
        let ctx = make_x86_64_ctx();
        let out = make_var("tmp:out", 1, 4);
        let eax = make_var("eax", 1, 4);
        let c1 = make_var("tmp:c1", 1, 4);
        let z1 = make_var("tmp:z1", 1, 8);
        let cast = make_var("tmp:cast", 1, 8);
        let trunc = make_var("tmp:t1", 1, 4);
        let block = make_block(vec![
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
            SSAOp::CallDefine { dst: eax.clone() },
            SSAOp::Copy {
                dst: c1.clone(),
                src: eax,
            },
            SSAOp::IntZExt {
                dst: z1.clone(),
                src: c1,
            },
            SSAOp::Cast {
                dst: cast.clone(),
                src: z1,
            },
            SSAOp::Trunc {
                dst: trunc.clone(),
                src: cast,
            },
            SSAOp::Copy {
                dst: out.clone(),
                src: trunc,
            },
        ]);

        assert_eq!(
            ctx.local_post_call_source_for_ssa_name_in_block(&block, &out.display_name(), 0),
            Some((block.addr, 0)),
            "copy-like chains must preserve the producing call source"
        );
    }

    #[test]
    fn local_post_call_source_allows_depth_sixteen_but_limits_long_chains() {
        let ctx = make_x86_64_ctx();
        let rax = make_var("rax", 1, 8);
        let direct = make_block(vec![
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
            SSAOp::CallDefine { dst: rax.clone() },
        ]);
        assert_eq!(
            ctx.local_post_call_source_for_ssa_name_in_block(&direct, &rax.display_name(), 16),
            Some((direct.addr, 0)),
            "depth 16 is still inside the recursion budget"
        );

        let mut ops = vec![
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
            SSAOp::CallDefine { dst: rax.clone() },
        ];
        let mut prev = rax;
        for idx in 0..18 {
            let next = make_var(&format!("tmp:chain{idx}"), 1, 8);
            ops.push(SSAOp::Copy {
                dst: next.clone(),
                src: prev,
            });
            prev = next;
        }
        let chained = make_block(ops);

        assert!(
            ctx.local_post_call_source_for_ssa_name_in_block(&chained, &prev.display_name(), 0)
                .is_none(),
            "copy-like source tracing must stop at the recursion budget"
        );
    }

    #[test]
    fn local_post_call_source_traces_stack_reload_to_call_result() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x1000, 0);
        let rax = make_var("rax", 1, 8);
        let slot = make_var("tmp:slot", 1, 8);
        let loaded = make_var("tmp:loaded", 1, 8);
        let copied = make_var("rdi", 1, 8);
        ctx.state
            .analysis_ctx
            .ownership
            .alias_sources
            .insert(rax.display_name(), CallSiteId::from(source_call));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            slot.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(-8),
            ),
        );
        let block = make_block(vec![
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
            SSAOp::CallDefine { dst: rax.clone() },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot.clone(),
                val: rax,
            },
            SSAOp::Load {
                dst: loaded.clone(),
                space: r2il::SpaceId::Ram,
                addr: slot,
            },
            SSAOp::Copy {
                dst: copied.clone(),
                src: loaded,
            },
        ]);

        assert_eq!(
            ctx.local_post_call_source_for_ssa_name_in_block(&block, &copied.display_name(), 0),
            Some(source_call),
            "stack reloads must preserve the canonical producing call source"
        );
    }

    #[test]
    fn local_post_call_source_refuses_custom_space_stack_shaped_reload() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x1000, 0);
        let rax = make_var("rax", 1, 8);
        let slot = make_var("tmp:slot", 1, 8);
        let loaded = make_var("tmp:loaded", 1, 8);
        ctx.state
            .analysis_ctx
            .ownership
            .alias_sources
            .insert(rax.display_name(), CallSiteId::from(source_call));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            slot.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(-8),
            ),
        );
        let block = make_block(vec![
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
            SSAOp::CallDefine { dst: rax.clone() },
            SSAOp::Store {
                space: r2il::SpaceId::Custom(7),
                addr: slot.clone(),
                val: rax,
            },
            SSAOp::Load {
                dst: loaded.clone(),
                space: r2il::SpaceId::Custom(7),
                addr: slot,
            },
        ]);

        assert!(
            ctx.local_post_call_source_for_ssa_name_in_block(&block, &loaded.display_name(), 0,)
                .is_none(),
            "stack-shaped accesses in a custom address space cannot inherit a RAM call-result home"
        );
    }

    #[test]
    fn local_post_call_source_refuses_mismatched_stack_reload_offset() {
        let mut ctx = make_x86_64_ctx();
        let source_call = (0x1000, 0);
        let rax = make_var("rax", 1, 8);
        let stored_slot = make_var("tmp:stored_slot", 1, 8);
        let loaded_slot = make_var("tmp:loaded_slot", 1, 8);
        let loaded = make_var("tmp:loaded", 1, 8);
        ctx.state
            .analysis_ctx
            .ownership
            .alias_sources
            .insert(rax.display_name(), CallSiteId::from(source_call));
        ctx.state.analysis_ctx.use_info.definitions.insert(
            stored_slot.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(-8),
            ),
        );
        ctx.state.analysis_ctx.use_info.definitions.insert(
            loaded_slot.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(-16),
            ),
        );
        let block = make_block(vec![
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
            SSAOp::CallDefine { dst: rax.clone() },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: stored_slot,
                val: rax,
            },
            SSAOp::Load {
                dst: loaded.clone(),
                space: r2il::SpaceId::Ram,
                addr: loaded_slot,
            },
        ]);

        assert!(
            ctx.local_post_call_source_for_ssa_name_in_block(&block, &loaded.display_name(), 0)
                .is_none(),
            "stack reload tracing must require the store and load offsets to match"
        );
    }

    #[test]
    fn local_post_call_source_limits_stack_reload_value_chain_depth() {
        let mut ctx = make_x86_64_ctx();
        let rax = make_var("rax", 1, 8);
        let slot = make_var("tmp:slot", 1, 8);
        let loaded = make_var("tmp:loaded", 1, 8);
        ctx.state.analysis_ctx.use_info.definitions.insert(
            slot.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(-8),
            ),
        );

        let mut ops = vec![
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
            SSAOp::CallDefine { dst: rax.clone() },
        ];
        let mut prev = rax;
        for idx in 0..16 {
            let next = make_var(&format!("tmp:reload_chain{idx}"), 1, 8);
            ops.push(SSAOp::Copy {
                dst: next.clone(),
                src: prev,
            });
            prev = next;
        }
        ops.push(SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr: slot.clone(),
            val: prev,
        });
        ops.push(SSAOp::Load {
            dst: loaded.clone(),
            space: r2il::SpaceId::Ram,
            addr: slot,
        });
        let block = make_block(ops);

        assert!(
            ctx.local_post_call_source_for_ssa_name_in_block(&block, &loaded.display_name(), 0)
                .is_none(),
            "stack reload source tracing must enforce the recursion budget"
        );
    }

    #[test]
    fn consumed_immediate_call_home_store_requires_adjacent_call_arguments() {
        let mut ctx = make_x86_64_ctx();
        let addr = make_var("tmp:home_addr", 1, 8);
        let val = make_var("tmp:home_val", 1, 8);
        let store = SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr: addr.clone(),
            val: val.clone(),
        };
        let block = make_block(vec![
            store.clone(),
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
        ]);
        ctx.state
            .analysis_ctx
            .use_info
            .consumed_by_call
            .insert(addr.display_name());
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((block.addr, 1), vec![call_arg(CExpr::IntLit(7))]);

        assert!(ctx.is_consumed_immediate_call_home_store(&block, 0, &store));

        ctx.state.analysis_ctx.use_info.call_args.clear();
        assert!(
            !ctx.is_consumed_immediate_call_home_store(&block, 0, &store),
            "a consumed store is not a call home without callsite argument proof"
        );
    }

    #[test]
    fn consumed_immediate_call_home_store_requires_consumed_marker() {
        let mut ctx = make_x86_64_ctx();
        let addr = make_var("tmp:home_addr", 1, 8);
        let val = make_var("tmp:home_val", 1, 8);
        let store = SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr,
            val,
        };
        let block = make_block(vec![
            store.clone(),
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
        ]);
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((block.addr, 1), vec![call_arg(CExpr::IntLit(7))]);

        assert!(
            !ctx.is_consumed_immediate_call_home_store(&block, 0, &store),
            "call-home suppression requires a consumed-by-call marker"
        );
    }

    #[test]
    fn consumed_immediate_call_home_store_stops_at_control_flow_and_named_locals() {
        let mut ctx = make_x86_64_ctx();
        let addr = make_var("tmp:home_addr", 1, 8);
        let val = make_var("tmp:home_val", 1, 8);
        let store = SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr: addr.clone(),
            val,
        };
        ctx.state
            .analysis_ctx
            .use_info
            .consumed_by_call
            .insert(addr.display_name());
        let branch_block = make_block(vec![
            store.clone(),
            SSAOp::Branch {
                target: make_var("ram:2000", 0, 8),
            },
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
        ]);
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((branch_block.addr, 2), vec![call_arg(CExpr::IntLit(7))]);

        assert!(
            !ctx.is_consumed_immediate_call_home_store(&branch_block, 0, &store),
            "control-flow boundaries must block immediate call-home classification"
        );

        ctx.state.analysis_ctx.use_info.definitions.insert(
            addr.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(-8),
            ),
        );
        ctx.state
            .analysis_ctx
            .stack_info
            .stack_vars
            .insert(-8, "buf".to_string());
        let call_block = make_block(vec![
            store.clone(),
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
        ]);
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((call_block.addr, 1), vec![call_arg(CExpr::IntLit(7))]);

        assert!(
            !ctx.is_consumed_immediate_call_home_store(&call_block, 0, &store),
            "stores to real named locals must not be hidden as transient call homes"
        );
    }

    #[test]
    fn consumed_immediate_call_home_store_keeps_frame_offset_zero_allowed() {
        let mut ctx = make_x86_64_ctx();
        let addr = make_var("tmp:home_addr", 1, 8);
        let val = make_var("tmp:home_val", 1, 8);
        let store = SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr: addr.clone(),
            val,
        };
        ctx.state
            .analysis_ctx
            .use_info
            .consumed_by_call
            .insert(addr.display_name());
        ctx.state.analysis_ctx.use_info.definitions.insert(
            addr.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(0),
            ),
        );
        ctx.state
            .analysis_ctx
            .stack_info
            .stack_vars
            .insert(0, "base_slot".to_string());
        let block = make_block(vec![
            store.clone(),
            SSAOp::Call {
                target: make_var("ram:401000", 0, 8),
            },
        ]);
        ctx.state
            .analysis_ctx
            .use_info
            .call_args
            .insert((block.addr, 1), vec![call_arg(CExpr::IntLit(7))]);

        assert!(
            ctx.is_consumed_immediate_call_home_store(&block, 0, &store),
            "frame offset zero is not a negative local slot and must stay eligible"
        );
    }

    #[test]
    fn post_call_stack_store_does_not_fabricate_call_result_owner() {
        fn stable_owner_with_post_call_store_value<F>(
            offset: i64,
            store_value: Varnode,
            install_function_facts: bool,
            seed_source: F,
        ) -> Option<String>
        where
            F: FnOnce(&mut FoldingContext<'_>, &str, (u64, usize)) -> BTreeSet<String>,
        {
            let mut arch = make_test_arch_x86_64();
            if install_function_facts {
                arch.add_register(RegisterDef::new("RIP", 0x30, 8));
            }
            let mut entry = R2ILBlock::new(0x1000, 4);
            entry.push(R2ILOp::Call {
                target: Varnode::constant(0x401050, 8),
            });
            if offset < 0 {
                entry.push(R2ILOp::IntSub {
                    dst: Varnode::unique(0x1200, 8),
                    a: Varnode::register(0x20, 8),
                    b: Varnode::constant(offset.unsigned_abs(), 8),
                });
            } else {
                entry.push(R2ILOp::IntAdd {
                    dst: Varnode::unique(0x1200, 8),
                    a: Varnode::register(0x20, 8),
                    b: Varnode::constant(offset as u64, 8),
                });
            }
            entry.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::unique(0x1200, 8),
                val: store_value,
            });

            let prepared = if install_function_facts {
                let register_storage = |offset| r2ssa::CanonicalStorageId {
                    space: r2ssa::CanonicalStorageSpace::Register,
                    offset,
                    size: 8,
                };
                let frame_pointer = register_storage(0x20);
                let stack_pointer = register_storage(0x28);
                let return_address = register_storage(0x30);
                let interface = r2ssa::SourceFunctionInterface::new_exact(
                    b"post-call-stack-owner:v1".to_vec(),
                    "sysv64",
                    [],
                    r2ssa::SourceFunctionReturn::Void,
                    [r2ssa::SourceStackSlotSpec::new_local(
                        r2ssa::StackAddressBase::FramePointer,
                        frame_pointer,
                        offset,
                        8,
                    )],
                )
                .and_then(|interface| interface.with_return_address_storage(return_address))
                .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
                .and_then(|interface| interface.with_frame_pointer_storage(frame_pointer))
                .expect("exact frame-local source interface");
                source_owned_fixture(
                    r2ssa::SsaArtifact::for_decompile_with_interface(
                        &[entry],
                        Some(&arch),
                        interface,
                    )
                    .expect("prepared exact stack-owner fixture")
                    .with_name("stack_owner_exact"),
                )
            } else {
                prepared_from_r2il_blocks(&[entry], &arch).with_name("stack_owner_fallback")
            };
            let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
            if install_function_facts {
                let source_call = (0x1000, 0);
                let call_result_facts = test_call_result_facts(&prepared);
                let (object, owner_offset) = call_result_facts
                    .results_for_site(r2types::CallsiteKey {
                        block_addr: source_call.0,
                        op_index: source_call.1,
                    })
                    .find_map(|fact| match fact.owner {
                        Some(r2ssa::ValueOwner::StackSlot { object, offset }) => {
                            Some((object, offset))
                        }
                        _ => None,
                    })
                    .expect("exact source interface must derive the call-result stack owner");
                let slot = prepared
                    .certificates()
                    .stack_slots
                    .get(&object)
                    .expect("derived owner must reference a certified stack slot");
                assert_eq!(
                    (slot.space, slot.base, slot.offset),
                    (SpaceId::Ram, r2ssa::StackAddressBase::FramePointer, offset,),
                    "derived owner must retain the declared RAM frame-local identity"
                );
                assert_eq!(owner_offset, offset);
                let render_facts = test_render_facts(&prepared);
                mutate_function_facts(&mut ctx, |function_facts| {
                    function_facts.replace_type_facts(r2types::FunctionTypeFacts {
                        stack_slots: BTreeMap::from([(
                            StackSlotKey {
                                base: ExternalStackBase::FramePointer,
                                offset,
                            },
                            r2types::ExternalStackSlotSpec {
                                name: "buf".to_string(),
                                ty: Some(r2types::CTypeLike::Int {
                                    bits: 64,
                                    signedness: r2types::Signedness::Unsigned,
                                }),
                                role: r2types::ExternalStackSlotRole::Local,
                                ..r2types::ExternalStackSlotSpec::default()
                            },
                        )]),
                        ..r2types::FunctionTypeFacts::default()
                    });
                    function_facts.set_call_results(call_result_facts);
                });
                assert_eq!(
                    ctx.inputs.function_facts.render_facts(),
                    &render_facts,
                    "exact frame-local source must produce the retained render facts"
                );
            }
            ctx.set_external_stack_vars(HashMap::from([(
                -8,
                stack_var_spec("buf", Some(CType::ptr(CType::Int(8))), Some("rbp")),
            )]));
            let blocks = prepared.function().blocks().cloned().collect::<Vec<_>>();
            ctx.analyze_blocks(&blocks);
            let block = prepared.function().get_block(0x1000).expect("entry");
            let call_idx = block
                .ops
                .iter()
                .position(|op| matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }))
                .expect("call op");
            let (store_idx, store_val) = block
                .ops
                .iter()
                .enumerate()
                .skip(call_idx + 1)
                .find_map(|(idx, op)| match op {
                    SSAOp::Store { val, .. } => Some((idx, val.display_name())),
                    _ => None,
                })
                .expect("post-call store");
            let source_call = (block.addr, call_idx);
            assert!(
                store_idx > call_idx,
                "test setup requires a post-call store"
            );
            let aliases = seed_source(&mut ctx, &store_val, source_call);

            let _ = aliases;
            ctx.stable_owned_call_result_name_for_source(source_call)
        }

        let rbp_input = Varnode::register(0x20, 8);
        assert_eq!(
            stable_owner_with_post_call_store_value(
                -8,
                rbp_input.clone(),
                false,
                |_, store_val, _| { BTreeSet::from([store_val.to_string()]) }
            ),
            None,
            "alias-set ownership must not fabricate a post-call stack-local result owner"
        );
        assert_eq!(
            stable_owner_with_post_call_store_value(
                -8,
                rbp_input.clone(),
                false,
                |ctx, store_val, source_call| {
                    ctx.state
                        .analysis_ctx
                        .use_info
                        .call_result_source_by_alias
                        .insert(store_val.to_string(), source_call);
                    BTreeSet::new()
                }
            ),
            None,
            "exact source map ownership must not fabricate a post-call stack-local result owner"
        );
        assert_eq!(
            stable_owner_with_post_call_store_value(
                -8,
                rbp_input.clone(),
                false,
                |ctx, store_val, source_call| {
                    ctx.state
                        .analysis_ctx
                        .use_info
                        .call_result_source_by_alias
                        .insert(store_val.to_ascii_lowercase(), source_call);
                    BTreeSet::new()
                }
            ),
            None,
            "lower-case source map ownership must not fabricate a post-call stack-local result owner"
        );
        assert_eq!(
            stable_owner_with_post_call_store_value(
                -8,
                Varnode::register(0x00, 8),
                true,
                |_, _, _| { BTreeSet::new() }
            ),
            Some("buf".to_string()),
            "prepared SSA call-result certificates may authorize a stack-local result owner"
        );
        assert_eq!(
            stable_owner_with_post_call_store_value(
                -8,
                rbp_input.clone(),
                false,
                |ctx, store_val, source_call| {
                    ctx.state
                        .analysis_ctx
                        .use_info
                        .call_result_source_by_alias
                        .insert(store_val.to_string(), (source_call.0, source_call.1 + 1));
                    BTreeSet::new()
                }
            ),
            None,
            "wrong exact source map entries must not bind a post-call stack local"
        );
        assert_eq!(
            stable_owner_with_post_call_store_value(
                -8,
                rbp_input.clone(),
                false,
                |ctx, store_val, source_call| {
                    ctx.state
                        .analysis_ctx
                        .use_info
                        .call_result_source_by_alias
                        .insert(
                            store_val.to_ascii_lowercase(),
                            (source_call.0, source_call.1 + 1),
                        );
                    BTreeSet::new()
                }
            ),
            None,
            "wrong lower-case source map entries must not bind a post-call stack local"
        );
        assert_eq!(
            stable_owner_with_post_call_store_value(8, rbp_input, false, |_, store_val, _| {
                BTreeSet::from([store_val.to_string()])
            }),
            None,
            "positive frame offsets must not become owned local result names"
        );
    }

    #[test]
    fn post_call_stack_store_after_next_call_does_not_fabricate_call_result_owner() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Call {
            target: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::constant(0x401060, 8),
        });
        entry.push(R2ILOp::IntSub {
            dst: Varnode::unique(0x1200, 8),
            a: Varnode::register(0x20, 8),
            b: Varnode::constant(8, 8),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x1200, 8),
            val: Varnode::register(0x00, 8),
        });

        let prepared =
            prepared_from_r2il_blocks(&[entry], &arch).with_name("stack_owner_call_boundary");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        ctx.set_external_stack_vars(HashMap::from([(
            -8,
            stack_var_spec("buf", Some(CType::ptr(CType::Int(8))), Some("rbp")),
        )]));
        let blocks = prepared.function().blocks().cloned().collect::<Vec<_>>();
        ctx.analyze_blocks(&blocks);
        let block = prepared.function().get_block(0x1000).expect("entry");
        let first_call_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }))
            .expect("first call");
        let store_val = block
            .ops
            .iter()
            .find_map(|op| match op {
                SSAOp::Store { val, .. } => Some(val.display_name()),
                _ => None,
            })
            .expect("store val");
        let source_call = (block.addr, first_call_idx);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_source_by_alias
            .insert(store_val.clone(), source_call);

        assert_eq!(
            {
                let _aliases = BTreeSet::from([store_val]);
                ctx.stable_owned_call_result_name_for_source(source_call)
            },
            None,
            "post-call stack stores after another call must not fabricate result owners"
        );
    }
}
