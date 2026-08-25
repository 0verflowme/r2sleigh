#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        collections::{BTreeMap, BTreeSet, HashMap, HashSet},
        ops::Deref,
        sync::Arc,
    };

    use crate::analysis::PtrArith;

    /// Say a value is read `count` times.
    ///
    /// Counts are kept against identities, so a test has to give the value one
    /// before it can claim anything about how often it is read.
    fn mark_use_counted(ctx: &mut FoldingContext<'_>, var: &SSAVar, count: usize) {
        let info = &mut ctx.state.analysis_ctx.use_info;
        if info.exact_value_id_for_var(var).is_none() {
            // Reuse whatever identity the name already has. Minting a second one
            // for the same spelling makes it ambiguous, and an ambiguous name
            // answers nothing.
            let next = info
                .value_id_for_name_or_bind(&var.display_name())
                .unwrap_or(r2ssa::ValueId(9000 + info.value_ids_by_var.len() as u32));
            let _ = info.bind_value_id(var, next);
        }
        for _ in 0..count {
            info.note_use_for_var(var);
        }
    }

    /// The same, for a test that only has the rendered spelling.
    ///
    /// The name is bound to an identity directly rather than through a
    /// reconstructed `SSAVar`: `SSAVar::new("v3ea00", 0, 8).display_name()` is
    /// `v3ea00_0`, so building a variable from a spelling files the count under
    /// a different name than the one the test asks about.
    fn mark_use_by_name(ctx: &mut FoldingContext<'_>, name: &str, count: usize) {
        let info = &mut ctx.state.analysis_ctx.use_info;
        if let Some(value_id) = info.value_id_for_name_or_bind(name) {
            *info.use_counts_by_value.entry(value_id).or_insert(0) += count;
        }
    }

    /// Record that a condition was decided by this value.
    ///
    /// It may already have an identity from `mark_use_counted`, so bind only
    /// when there is nothing there.
    fn bind_and_mark_condition(ctx: &mut FoldingContext<'_>, var: &SSAVar) {
        let info = &mut ctx.state.analysis_ctx.use_info;
        if info.exact_value_id_for_var(var).is_none() {
            let next = info
                .value_id_for_name_or_bind(&var.display_name())
                .unwrap_or(r2ssa::ValueId(9000 + info.value_ids_by_var.len() as u32));
            let _ = info.bind_value_id(var, next);
        }
        info.note_condition_var(var);
    }
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

    /// A debug rendering with each identifier replaced by what it spells.
    ///
    /// Assertions here ask whether an expression mentions a name. A reference
    /// carries an identifier rather than a spelling, so the spelling has to be
    /// read back out of the table that issued it.
    fn spelled(ctx: &FoldingContext<'_>, expr: &CExpr) -> String {
        let raw = format!("{expr:?}");
        let pattern = regex_lite_symbol_ids(&raw);
        let mut out = raw.clone();
        for (whole, index) in pattern {
            let id_expr = ctx
                .symbols
                .borrow()
                .iter()
                .find(|(id, _)| id.index() == index)
                .map(|(_, symbol)| symbol.name.to_string());
            if let Some(name) = id_expr {
                out = out.replace(&whole, &name);
            }
        }
        out
    }

    /// Every `SymbolId { .. }` in a debug rendering, with its position.
    fn regex_lite_symbol_ids(text: &str) -> Vec<(String, usize)> {
        let mut found = Vec::new();
        let mut rest = text;
        while let Some(start) = rest.find("SymbolId { table: TableId(") {
            let Some(end) = rest[start..].find(" }") else {
                break;
            };
            let whole = &rest[start..start + end + 2];
            if let Some(idx) = whole.rfind("index: ") {
                let digits: String = whole[idx + 7..]
                    .chars()
                    .take_while(|c| c.is_ascii_digit())
                    .collect();
                if let Ok(index) = digits.parse::<usize>() {
                    found.push((whole.to_string(), index));
                }
            }
            rest = &rest[start + end + 2..];
        }
        found
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
        // The architecture says where it returns a value, so a call result is
        // distinguishable without a list of register spellings.
        arch.return_registers = vec![RegisterDef::new("RAX", 0x00, 8)];
        arch
    }

    fn make_test_arch_aarch64_kernel_regs() -> ArchSpec {
        let mut arch = ArchSpec::new("aarch64");
        arch.add_register(RegisterDef::new("x0", 0x4000, 8));
        arch.add_register(RegisterDef::sub("w0", 0x4000, 4, "x0"));
        arch.return_registers = vec![RegisterDef::new("x0", 0x4000, 8)];
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
        ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&alias.to_string(), source_call);
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
            flag_regs: crate::fold::arch::X86_FLAG_REGISTERS
                .iter()
                .map(|name| (*name).to_string())
                .collect(),
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
            materialized_edge_copies: crate::normalize::no_materialized_edge_copies(),
            display_names: crate::empty_display_names(),
            arch,
            function_names: empty_u64,
            strings: empty_u64,
            binary_symbols: empty_u64,
            function_facts: empty_function_facts(),
            certified_rendering_required: false,
            stack_slots: empty_stack_slots,
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
            flag_regs: crate::fold::arch::X86_FLAG_REGISTERS
                .iter()
                .map(|name| (*name).to_string())
                .collect(),
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
            materialized_edge_copies: crate::normalize::no_materialized_edge_copies(),
            display_names: crate::empty_display_names(),
            arch,
            function_names: empty_u64,
            strings: empty_u64,
            binary_symbols: empty_u64,
            function_facts: empty_function_facts(),
            certified_rendering_required: false,
            stack_slots: empty_stack_slots,
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
            expr_contains_var(&ctx, &sum_rhs, "sum") && !expr_contains_addr_of(&sum_rhs),
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

    fn expr_contains_flag_artifact(ctx: &FoldingContext<'_>, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                let lower = ctx.spelling(*name).to_lowercase();
                lower.starts_with("of_")
                    || lower.starts_with("zf_")
                    || lower.starts_with("sf_")
                    || lower.starts_with("cf_")
            }
            CExpr::Binary { left, right, .. } => {
                expr_contains_flag_artifact(ctx, left) || expr_contains_flag_artifact(ctx, right)
            }
            CExpr::Unary { operand, .. } => expr_contains_flag_artifact(ctx, operand),
            CExpr::Paren(inner) => expr_contains_flag_artifact(ctx, inner),
            CExpr::Cast { expr: inner, .. } => expr_contains_flag_artifact(ctx, inner),
            CExpr::Deref(inner) => expr_contains_flag_artifact(ctx, inner),
            CExpr::Subscript { base, index } => {
                expr_contains_flag_artifact(ctx, base) || expr_contains_flag_artifact(ctx, index)
            }
            CExpr::Member { base, .. } => expr_contains_flag_artifact(ctx, base),
            CExpr::PtrMember { base, .. } => expr_contains_flag_artifact(ctx, base),
            CExpr::Call { func, args, .. } => {
                expr_contains_flag_artifact(ctx, func) || args.iter().any(|a| expr_contains_flag_artifact(ctx, a))
            }
            _ => false,
        }
    }

    fn expr_contains_var(ctx: &FoldingContext<'_>, expr: &CExpr, target: &str) -> bool {
        match expr {
            CExpr::External { .. } => false,
            CExpr::Var(name) => &*ctx.spelling(*name) == target,
            CExpr::Unary { operand, .. }
            | CExpr::Paren(operand)
            | CExpr::Deref(operand)
            | CExpr::AddrOf(operand)
            | CExpr::Sizeof(operand)
            | CExpr::Cast { expr: operand, .. } => expr_contains_var(ctx, operand, target),
            CExpr::Binary { left, right, .. } => {
                expr_contains_var(ctx, left, target) || expr_contains_var(ctx, right, target)
            }
            CExpr::Subscript { base, index } => {
                expr_contains_var(ctx, base, target) || expr_contains_var(ctx, index, target)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                expr_contains_var(ctx, base, target)
            }
            CExpr::Call { func, args, .. } => {
                expr_contains_var(ctx, func, target)
                    || args.iter().any(|arg| expr_contains_var(&ctx, arg, target))
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                expr_contains_var(ctx, cond, target)
                    || expr_contains_var(ctx, then_expr, target)
                    || expr_contains_var(ctx, else_expr, target)
            }
            CExpr::Comma(items) => items.iter().any(|item| expr_contains_var(&ctx, item, target)),
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
            CExpr::Call { func, args, .. } => {
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
            CExpr::Call { func, args, .. } => {
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
            .insert_definition_for_name_if_absent("tmp:1_0", CExpr::IntLit(42));

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
            CExpr::External {
                name: "sym.local_two_arg".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            },
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
        );
        let normalized = ctx.normalize_call_expr_for_source_call(
            source_call,
            poisoned,
            FinalExprNormalizeContext::DefinitionRoot,
        );

        assert_eq!(
            normalized,
            CExpr::call_at(source_call, 
                CExpr::External {
                    name: "sym.imp.one_arg".to_string(),
                    kind: crate::symbol::ExternalKind::Import,
                },
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
                CExpr::External {
                    name: "sym.poisoned".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                },
                vec![CExpr::IntLit(7)],
            ),
            FinalExprNormalizeContext::DefinitionRoot,
        );

        assert_eq!(
            normalized,
            CExpr::call_at((0x1000, 0), 
                CExpr::External {
                    name: "sym.poisoned".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                },
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
                CExpr::External {
                    name: "sym.poisoned".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                },
                vec![CExpr::IntLit(7)],
            ),
            FinalExprNormalizeContext::DefinitionRoot,
        );

        assert_eq!(
            normalized,
            CExpr::call_at((0x1000, 0), CExpr::External { name: "sym.helper".to_string(), kind: crate::symbol::ExternalKind::Function }, vec![CExpr::IntLit(7)]),
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
            CExpr::External {
                name: "sym.imp.printf".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
            vec![ctx.name_ref("tmp_result")],
        );
        let normalized = ctx.normalize_call_expr_for_source_call(
            source_call,
            poisoned,
            FinalExprNormalizeContext::DefinitionRoot,
        );

        assert_eq!(
            normalized,
            CExpr::call_at(source_call, 
                CExpr::External {
                    name: "sym.local.helper".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                },
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
            CExpr::External {
                name: "sym.local_logger".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            },
            vec![
                CExpr::StringLit("x=%d".to_string()),
                imported_ctx.name_ref("x"),
                imported_ctx.name_ref("garbage"),
            ],
        );

        assert_eq!(
            imported_ctx.normalize_call_expr_for_source_call(
                imported_source,
                rendered_local_logger,
                FinalExprNormalizeContext::DefinitionRoot,
            ),
            CExpr::call_at(imported_source, 
                CExpr::External {
                    name: "sym.imp.printf".to_string(),
                    kind: crate::symbol::ExternalKind::Import,
                },
                vec![
                    CExpr::StringLit("x=%d".to_string()),
                    imported_ctx.name_ref("x"),
                    imported_ctx.name_ref("garbage"),
                ],
            ),
            "typed variadic printf callsite identity must preserve certified args; format strings are not arity proof",
        );

        let mut internal_ctx = FoldingContext::new(64);
        // Both contexts read one fixture, so one table between them.
        internal_ctx.symbols = std::rc::Rc::clone(&imported_ctx.symbols);
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
            CExpr::External {
                name: "sym.imp.printf".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
            vec![
                CExpr::StringLit("x=%d".to_string()),
                imported_ctx.name_ref("x"),
                imported_ctx.name_ref("garbage"),
            ],
        );

        assert_eq!(
            internal_ctx.normalize_call_expr_for_source_call(
                internal_source,
                poisoned_printf,
                FinalExprNormalizeContext::DefinitionRoot,
            ),
            CExpr::call_at((0x1000, 1), 
                CExpr::External {
                    name: "sym.local_logger".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                },
                vec![
                    CExpr::StringLit("x=%d".to_string()),
                    imported_ctx.name_ref("x"),
                    imported_ctx.name_ref("garbage"),
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
                    CExpr::External {
                        name: "sym.local_nested".to_string(),
                        kind: crate::symbol::ExternalKind::Function,
                    },
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
            CExpr::External {
                name: "sym.imp.nested_one_arg".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
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
            CExpr::External {
                name: "sym.imp.nested_one_arg".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
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
            CExpr::External {
                name: "sym.imp.nested_one_arg".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
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
                CExpr::External {
                    name: "sym.local_two_arg".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                },
                vec![CExpr::IntLit(7)],
            ),
        );

        let poisoned = CExpr::call(
            CExpr::External {
                name: "sym.local_two_arg".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            },
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
        );
        assert_eq!(
            ctx.normalize_call_expr_for_source_call(
                source_call,
                poisoned.clone(),
                FinalExprNormalizeContext::DefinitionRoot,
            ),
            CExpr::call_at(source_call, 
                CExpr::External {
                    name: "sym.imp.one_arg".to_string(),
                    kind: crate::symbol::ExternalKind::Import,
                },
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
                CExpr::External {
                    name: "sym.local_two_arg".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                },
                vec![CExpr::IntLit(7)],
            ),
        );

        let rendered = CExpr::call(
            CExpr::External {
                name: "sym.imp.one_arg".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
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
            CExpr::External {
                name: "sym.imp.one_arg".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
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
                CExpr::External {
                    name: "sym.local_two_arg".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                },
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
                CExpr::call_at(source_call, 
                    CExpr::External {
                        name: "sym.imp.one_arg".to_string(),
                        kind: crate::symbol::ExternalKind::Import,
                    },
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent("X20_1", CExpr::call(
                CExpr::External {
                    name: "sym.imp.one_arg".to_string(),
                    kind: crate::symbol::ExternalKind::Import,
                },
                vec![CExpr::IntLit(7)],
            ),
        );
        mark_use_by_name(&mut ctx, "x20_1", 1);

        let rendered = CExpr::call(
            CExpr::External {
                name: "sym.imp.one_arg".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
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
                CExpr::External {
                    name: "sym.local_two_arg".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                },
                vec![CExpr::IntLit(7), CExpr::IntLit(9)],
            ),
        );

        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs_for_visible_name({ let CExpr::Var(id) = ctx.name_ref("owned_result") else { unreachable!() }; id }),
            Some(CExpr::call_at(source_call, 
                CExpr::External {
                    name: "sym.imp.one_arg".to_string(),
                    kind: crate::symbol::ExternalKind::Import,
                },
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
                CExpr::External {
                    name: "sym.local.poisoned".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                },
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
            CExpr::External {
                name: "sym.local_two_arg".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            },
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
            CExpr::External {
                name: "sym.local_two_arg".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            },
            vec![CExpr::IntLit(7), CExpr::IntLit(9)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, source_expr.clone());

        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs("owned_result", &source_expr),
            Some(CExpr::call_at(source_call, 
                CExpr::External {
                    name: "sym.imp.one_arg".to_string(),
                    kind: crate::symbol::ExternalKind::Import,
                },
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
            Some(CExpr::call_at((0x1000, 0), 
                CExpr::External {
                    name: "sym.imp.one_arg".to_string(),
                    kind: crate::symbol::ExternalKind::Import,
                },
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
                CExpr::External {
                    name: "sym.local_two_arg".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                },
                vec![CExpr::IntLit(7), CExpr::IntLit(9)],
            ),
        );

        assert_eq!(
            ctx.recovered_owned_call_result_definition_rhs(
                "owned_result",
                &ctx.name_ref("tmp_result"),
            ),
            Some(CExpr::call_at((0x1000, 0), 
                CExpr::External {
                    name: "sym.imp.one_arg".to_string(),
                    kind: crate::symbol::ExternalKind::Import,
                },
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
                CExpr::External {
                    name: "sym.imp.printf".to_string(),
                    kind: crate::symbol::ExternalKind::Import,
                },
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
                        CExpr::External {
                            name: "sym._unlock".to_string(),
                            kind: crate::symbol::ExternalKind::Function,
                        },
                        vec![
                            ctx.name_ref("argc"),
                            ctx.name_ref("argc"),
                            CExpr::call(
                                CExpr::External {
                                    name: "sym.imp.atoi".to_string(),
                                    kind: crate::symbol::ExternalKind::Import,
                                },
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
            CExpr::External {
                name: "sym._unlock".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            },
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
                        CExpr::External {
                            name: "sym._solve_equation".to_string(),
                            kind: crate::symbol::ExternalKind::Function,
                        },
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
                        CExpr::External {
                            name: "sym._complex_check".to_string(),
                            kind: crate::symbol::ExternalKind::Function,
                        },
                        vec![
                            ctx.name_ref("argc"),
                            CExpr::call(
                                CExpr::External {
                                    name: "sym.imp.atoi".to_string(),
                                    kind: crate::symbol::ExternalKind::Import,
                                },
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
            .insert_call_result_source_alias(&owner.display_name(), (0x1000, 0));
        ctx.state
            .analysis_ctx
            .use_info
            .insert_call_result_source_alias(&shadow.display_name(), (0x1000, 0));
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
                    CExpr::External {
                        name: "sym.imp.malloc".to_string(),
                        kind: crate::symbol::ExternalKind::Import,
                    },
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
            .insert_call_result_source_alias(&owner.display_name(), (0x1000, 0));
        ctx.state
            .analysis_ctx
            .use_info
            .insert_call_result_source_alias(&shadow.display_name(), (0x1000, 0));
        ctx.state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert(owner.display_name(), "buf".to_string());
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&shadow.display_name(), CExpr::call(
                CExpr::External {
                    name: "sym.imp.malloc".to_string(),
                    kind: crate::symbol::ExternalKind::Import,
                },
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

        let callee = CExpr::External { name: "sym.helper".to_string(), kind: crate::symbol::ExternalKind::Function };
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
            CExpr::External {
                name: "sym.imp.free".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
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
            CExpr::External {
                name: "sym.local.rendered_name".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            },
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
            CExpr::External {
                name: "sym.local.poison".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            },
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
        fn lowered_lhs_for(dst: SSAVar) -> String {
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
            let CExpr::Var(name) = *left else {
                panic!("expected a reference on the left");
            };
            ctx.spelling(name).to_string()
        }

        assert_eq!(
            lowered_lhs_for(make_var("reg:10", 2, 8)),
            "r10_2"
        );
        assert_eq!(
            lowered_lhs_for(make_var("reg:zf", 2, 1)),
            "zf_2"
        );
        assert_eq!(
            lowered_lhs_for(make_var("tmp:11f80", 2, 8)),
            "t2"
        );
        assert_eq!(
            lowered_lhs_for(make_var("unique:11f80", 2, 8)),
            "t2"
        );
        assert_eq!(
            lowered_lhs_for(make_var("TMP:11f80", 2, 8)),
            "tmp_11f80_2"
        );
        assert_eq!(
            lowered_lhs_for(make_var("reg:10", 0, 8)),
            "arg1"
        );
    }

    #[test]
    fn should_inline_ssavar_guard_matrix_preserves_refusal_order() {
    
    fn mark_use(ctx: &mut FoldingContext<'_>, var: &SSAVar, count: usize) {
        mark_use_counted(ctx, var, count);
    }

        fn mark_simple_def(ctx: &mut FoldingContext<'_>, var: &SSAVar) {
            ctx.state
                .analysis_ctx
                .use_info
                .insert_definition_for_name_if_absent(&var.display_name(), CExpr::IntLit(1));
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
            .insert_call_result_source_alias(&direct_unowned.display_name(), (0x1000, 1));
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
            .insert_call_result_source_alias(&direct_owned.display_name(), (0x1000, 2));
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
        bind_and_mark_condition(&mut ctx, &condition_non_candidate);
        assert!(!ctx.should_inline(&condition_non_candidate));

        let condition_flag = make_var("ZF", 1, 1);
        mark_use(&mut ctx, &condition_flag, 1);
        bind_and_mark_condition(&mut ctx, &condition_flag);
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
        ctx.state
            .analysis_ctx
            .use_info
            .insert_definition_for_name_if_absent(&single_ordinary.display_name(), CExpr::IntLit(7));
        assert!(ctx.should_inline(&single_ordinary));

        // Leaving the statement out says the reader will inline the value, so a
        // value nothing can render keeps its statement rather than its name
        // being printed with nothing defining it.
        let single_unrenderable = make_var("ordinary_single_unrenderable", 1, 8);
        mark_use(&mut ctx, &single_unrenderable, 1);
        assert!(!ctx.should_inline(&single_unrenderable));

        let stack_base = make_var("RSP", 1, 8);
        mark_use(&mut ctx, &stack_base, 1);
        assert!(!ctx.should_inline(&stack_base));

        let return_reg = make_var("RAX", 1, 8);
        mark_use(&mut ctx, &return_reg, 1);
        ctx.state
            .analysis_ctx
            .use_info
            .insert_definition_for_name_if_absent(&return_reg.display_name(), CExpr::IntLit(9));
        assert!(ctx.should_inline(&return_reg));
        ctx.state.return_blocks.insert(0x2000);
        ctx.current_block_addr.set(Some(0x2000));
        assert!(!ctx.should_inline(&return_reg));
        ctx.current_block_addr.set(None);
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&ret.display_name(), CExpr::binary(
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&ret.display_name(), CExpr::binary(
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
        ctx.state.analysis_ctx.use_info.insert_ptr_arith_for_var(
            &addr,
            PtrArith {
                base: arr.clone(),
                index: bogus_index.clone(),
                element_size: 4,
                is_sub: false,
            },
        );
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&bogus_index.display_name(), ctx.name_ref("local_8"),
        );
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&addr.display_name(), CExpr::binary(
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
            .insert_definition_for_name_if_absent(&real_index.display_name(), ctx.name_ref("local_c"));
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&real_index.display_name(), crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Expr(CExpr::Var(
                { let CExpr::Var(id) = ctx.name_ref("local_c") else { unreachable!() }; id },
            ))),
        );
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&load.display_name(), crate::analysis::SemanticValue::Load {
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
                    .semantic_value_for_name(&load.display_name())
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
            CExpr::Call { ref func, ref args, .. }
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
        ctx.state.analysis_ctx.use_info.insert_stack_slot_for_name(&"len".to_string(), StackSlotProvenance {
                offset: -0x20,
                predicate_carrier: false,
                return_carrier: false,
                value_kind: StackSlotValueKind::Scalar,
            },
        );
        ctx.state.analysis_ctx.use_info.insert_stack_slot_for_name(&"buf".to_string(), StackSlotProvenance {
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
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&len_value.display_name(), crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Expr(CExpr::Var(
                { let CExpr::Var(id) = ctx.name_ref("len") else { unreachable!() }; id },
            ))),
        );
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&buf_value.display_name(), crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Expr(CExpr::Var(
                { let CExpr::Var(id) = ctx.name_ref("buf") else { unreachable!() }; id },
            ))),
        );
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&store_addr.display_name(), crate::analysis::SemanticValue::Load {
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
                    .semantic_value_for_name(&store_addr.display_name())
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&base.display_name(), CExpr::binary(
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
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&dst.display_name(), crate::analysis::SemanticValue::Load {
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
            .semantic_value_for_name(&dst.display_name())
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&addr.display_name(), CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("arg1"),
                CExpr::binary(
                    BinaryOp::Shl,
                    ctx.name_ref("arg2"),
                    CExpr::IntLit(2),
                ),
            ),
        );
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&dst.display_name(), crate::analysis::SemanticValue::Load {
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
                    .semantic_value_for_name(&dst.display_name())
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&addr.display_name(), CExpr::binary(
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
        ctx.inputs.binary_symbols = Box::leak(Box::new(HashMap::from([(
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
        ctx.inputs.binary_symbols = Box::leak(Box::new(HashMap::from([(
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&base.display_name(), CExpr::binary(
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
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&dst.display_name(), crate::analysis::SemanticValue::Load {
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
            .semantic_value_for_name(&dst.display_name())
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
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&addr.display_name(), crate::analysis::SemanticValue::Address(crate::analysis::NormalizedAddr {
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
        let rendered_text = spelled(&ctx, &rendered);
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
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&addr.display_name(), crate::analysis::SemanticValue::Address(crate::analysis::NormalizedAddr {
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
        let rendered_text = spelled(&ctx, &rendered);
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
        let rendered = spelled(&ctx, &semantic);
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
        let rendered_text = spelled(&ctx, &rendered);
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent("local_c", CExpr::binary(
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
        let rendered_text = spelled(&ctx, &rendered);
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
        let rendered_text = spelled(&ctx, &rendered);
        assert!(
            !rendered_text.contains("p0"),
            "field_name_any fallback must not manufacture placeholder member access, got {rendered:?}"
        );
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent("tmp:cond_1", CExpr::binary(
                BinaryOp::Eq,
                ctx.name_ref("result"),
                CExpr::IntLit(25),
            ),
        );
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent("result", CExpr::Deref(Box::new(CExpr::binary(
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent("tmp:cond_1", CExpr::binary(
                BinaryOp::Eq,
                ctx.name_ref("result"),
                CExpr::IntLit(19),
            ),
        );
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent("result", CExpr::Paren(Box::new(CExpr::Cast {
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent("tmp:cond_1", CExpr::binary(
                BinaryOp::Eq,
                ctx.name_ref("result"),
                CExpr::IntLit(19),
            ),
        );
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent("result", CExpr::binary(
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
            .insert_definition_for_name_if_absent("tmp:foo_2", ctx.name_ref("local_4"));
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent("tmp:11f80_19", CExpr::binary(
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
            .insert_definition_for_name_if_absent("tmp:raw_2", CExpr::IntLit(1));
        ctx.state
            .analysis_ctx
            .use_info
            .insert_definition_for_name_if_absent("value_2", CExpr::IntLit(2));
        ctx.state
            .analysis_ctx
            .use_info
            .insert_definition_for_name_if_absent("TMP:raw_2", CExpr::IntLit(3));

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
            .insert_definition_for_name_if_absent("src_1", ctx.name_ref("arg1"));
        // Bind before filing anything about `tmp:ret_1`: filing under a name
        // mints an identity, and a later bind of the same spelling would collide
        // and make the name ambiguous.
        let ret = r2ssa::SSAVar::new("tmp:ret", 1, 8);
        assert_eq!(
            ctx.state
                .analysis_ctx
                .use_info
                .bind_value_id(&ret, r2ssa::ValueId(902)),
            Some(r2ssa::ValueId(902))
        );
        let rax_2 = ctx.name_ref("rax_2");
        ctx.state
            .analysis_ctx
            .use_info
            .insert_definition_for_name_if_absent("tmp:ret_1", rax_2);
        ctx.state
            .analysis_ctx
            .use_info
            .insert_forwarded_value_for_var(
                &ret,
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
            .insert_definition_for_name_if_absent("sf_1", ctx.name_ref("sf_2"));
        ctx.state
            .analysis_ctx
            .use_info
            .insert_definition_for_name_if_absent("sf_2", ctx.name_ref("sf_1"));

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
            CExpr::External {
                name: "sym._IORWLockUnlock".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            },
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
            CExpr::External {
                name: "sym.imp.free".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
            vec![ctx.name_ref("ptr")],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["value_1".to_string()]));
        ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&"value_1".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        mark_use_by_name(&mut ctx, "value_1", 1);
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
            CExpr::External {
                name: "sym.imp.free".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
            vec![ctx.name_ref("ptr")],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["value_1".to_string()]));
        ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&"value_1".to_string(), source_call);
        mark_use_by_name(&mut ctx, "value_1", 1);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(ctx.name_ref("value_1"), call)),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts.clone());

        assert_eq!(
            pruned,
            vec![
                CStmt::Expr(CExpr::call(
                    CExpr::External {
                        name: "sym.imp.free".to_string(),
                        kind: crate::symbol::ExternalKind::Import,
                    },
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
            CExpr::External {
                name: "sym.local.rendered_name".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            },
            vec![ctx.name_ref("ptr")],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["value_1".to_string()]));
        ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&"value_1".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        mark_use_by_name(&mut ctx, "value_1", 1);
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
        ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&"x0_3".to_string(), source_call);
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
        ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&"v3ea00".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        mark_use_by_name(&mut ctx, "v3ea00", 1);
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
            CExpr::External {
                name: "sym.imp.alloc".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
            vec![CExpr::IntLit(32)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["RAX_6".to_string()]));
        ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&"RAX_6".to_string(), source_call);
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_exprs
            .insert(source_call, call.clone());
        mark_use_by_name(&mut ctx, "RAX_6", 1);
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
            CExpr::External {
                name: "sym.imp.alloc".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
            vec![CExpr::IntLit(32)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["RAX_6".to_string()]));
        ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&"RAX_6".to_string(), source_call);
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
            CExpr::External {
                name: "sym.imp.alloc".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
            vec![CExpr::IntLit(32)],
        );
        ctx.state
            .analysis_ctx
            .use_info
            .call_result_aliases
            .insert(source_call, BTreeSet::from(["RAX_6".to_string()]));
        ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&"RAX_6".to_string(), source_call);
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
            CExpr::External {
                name: "sym.imp.alloc".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
            vec![CExpr::IntLit(32)],
        );
        ctx.state.analysis_ctx.use_info.call_result_aliases.insert(
            source_call,
            BTreeSet::from(["value_1".to_string(), "value_2".to_string()]),
        );
        ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&"value_1".to_string(), source_call);
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
            CExpr::External {
                name: "sym.imp.alloc".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
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
            .insert_stack_slot_for_name("value_1", StackSlotProvenance::new(-8));
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
        // The context is x86-64, so the flags are spelled the way that target
        // spells them. This read tmpng and tmpzr, which are arm64 condition
        // codes, and passed only because the flag test accepted every
        // architecture's spellings at once.
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("sf_1"),
                CExpr::binary(BinaryOp::Lt, ctx.name_ref("sp"), CExpr::IntLit(0)),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("zf_1"),
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
    fn a_carrier_read_at_another_width_resolves_to_a_cast_of_the_carrier() {
        // The half of the location model an alias map cannot hold. `eax_5` is
        // not `rax`, it is `(uint32_t)rax`; answering with the carrier's name
        // alone renders the right identifier over the wrong value, which is what
        // a corpus measured in checksums reports as a collapse.
        let mut ctx = FoldingContext::new(64);
        ctx.carrier_member_views.insert(
            "EAX_2".to_string(),
            crate::normalize::CarrierMemberView {
                carrier: "rax".to_string(),
                width: 4,
                carrier_width: 8,
            },
        );
        // A carrier held narrow still answers a wide read, because a narrow
        // write clears the rest of the register.
        ctx.carrier_member_views.insert(
            "R8_2".to_string(),
            crate::normalize::CarrierMemberView {
                carrier: "r8d".to_string(),
                width: 8,
                carrier_width: 4,
            },
        );

        let narrowed = ctx.get_expr(&make_var("EAX", 2, 4));
        assert!(
            matches!(
                &narrowed,
                CExpr::Cast {
                    ty: CType::UInt(32),
                    expr,
                } if matches!(expr.as_ref(), CExpr::Var(name)
                    if &*ctx.spelling(*name) == "rax")
            ),
            "expected (uint32_t)rax, got {narrowed:?}"
        );

        let widened = ctx.get_expr(&make_var("R8", 2, 8));
        assert!(
            matches!(
                &widened,
                CExpr::Cast {
                    ty: CType::UInt(64),
                    expr,
                } if matches!(expr.as_ref(), CExpr::Var(name)
                    if &*ctx.spelling(*name) == "r8d")
            ),
            "expected (uint64_t)r8d, got {widened:?}"
        );
    }

    #[test]
    fn stack_frame_op_elides_the_entry_link_register_save_but_not_a_scratch_one() {
        // `stp x29, x30, [sp, N]` is the arm64 frame record. The link register
        // is not callee-saved -- a leaf may clobber it -- so the callee-saved
        // list never covered it, and a non-leaf function's prologue save came
        // out as a program statement. Only the value the function was entered
        // with is frame bookkeeping; a later value in x30 is a scratch use and
        // its store is real text.
        let mut ctx = FoldingContext::new(64);
        let addr = make_var("tmp:stack", 1, 8);
        ctx.state
            .analysis_ctx
            .use_info
            .insert_definition_for_name_if_absent(
                &addr.display_name(),
                CExpr::binary(BinaryOp::Sub, ctx.name_ref("rsp"), CExpr::IntLit(0x20)),
            );

        let entry_save = make_var("TMP:entry_lr", 1, 8);
        let scratch_save = make_var("TMP:scratch_lr", 1, 8);
        let x30_0 = r2ssa::SSAVar::new("x30", 0, 8);
        let x30_1 = r2ssa::SSAVar::new("x30", 1, 8);
        let info = &mut ctx.state.analysis_ctx.use_info;
        info.bind_value_id(&entry_save, r2ssa::ValueId(940));
        info.bind_value_id(&scratch_save, r2ssa::ValueId(941));
        info.bind_value_id(&x30_0, r2ssa::ValueId(942));
        info.bind_value_id(&x30_1, r2ssa::ValueId(943));
        info.insert_copy_source_for_vars(&entry_save, &x30_0);
        info.insert_copy_source_for_vars(&scratch_save, &x30_1);

        assert!(
            ctx.is_stack_frame_op(&SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: addr.clone(),
                val: entry_save,
            }),
            "saving the link register the function was entered with is prologue state"
        );
        assert!(
            !ctx.is_stack_frame_op(&SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr,
                val: scratch_save,
            }),
            "storing a later value of the link register is program text"
        );
    }

    #[test]
    fn stack_frame_op_uses_typed_temp_for_indirect_callee_saved_push() {
        let mut ctx = FoldingContext::new(64);
        let addr = make_var("tmp:stack", 1, 8);
        let saved = make_var("TMP:saved", 1, 8);
        // The temp has to point into the frame. Accepting any temp is what let
        // a field load into a callee-saved register pass as an epilogue pop.
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&addr.display_name(), CExpr::binary(BinaryOp::Sub, ctx.name_ref("rsp"), CExpr::IntLit(0x20)),
        );
        let rbx_1 = r2ssa::SSAVar::new("RBX", 1, 8);
        let info = &mut ctx.state.analysis_ctx.use_info;
        assert_eq!(info.bind_value_id(&saved, r2ssa::ValueId(930)), Some(r2ssa::ValueId(930)));
        assert_eq!(info.bind_value_id(&rbx_1, r2ssa::ValueId(931)), Some(r2ssa::ValueId(931)));
        info.insert_copy_source_for_vars(&saved, &rbx_1);

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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&field.display_name(), CExpr::binary(BinaryOp::Add, ctx.name_ref("RBX_1"), CExpr::IntLit(0x38)),
        );
        assert!(!ctx.is_stack_frame_op(&SSAOp::Load {
            dst: make_var("RBX", 2, 8),
            space: r2il::SpaceId::Ram,
            addr: field,
        }));
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
        let rendered = spelled(&ctx, &condition);
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
            CExpr::External {
                name: "sym.local_two_arg".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            },
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
            .insert_definition_for_name_if_absent("X20_1", poisoned_call.clone());
        mark_use_by_name(&mut ctx, "x20_1", 1);

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
            .insert_definition_for_name_if_absent("X20_1", definition_expr);
        mark_use_by_name(&mut ctx, "x20_1", 1);

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
            .insert_definition_for_name_if_absent("X20_1", definition_expr);
        mark_use_by_name(&mut ctx, "x20_1", 1);

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
            .insert_definition_for_name_if_absent("X20_1", helper_call.clone());
        mark_use_by_name(&mut ctx, "x20_1", 1);

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
            CExpr::call(CExpr::External { name: "sym.helper".to_string(), kind: crate::symbol::ExternalKind::Function }, vec![]),
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&addr.display_name(), CExpr::binary(
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
        assert!(!ctx.is_imported_call_target(&CExpr::External { name: "sym.helper".to_string(), kind: crate::symbol::ExternalKind::Function }));
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
            mark_use_by_name(ctx, &alias.to_ascii_lowercase(), 1);
        }


        let mut exact_ctx = make_aarch64_ctx();
        let helper_call = CExpr::call(
            CExpr::External {
                name: "sym.imp.helper".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
            vec![exact_ctx.name_ref("arg1")],
        );
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

        // One fixture read by three contexts, so one table between them.
        let mut ambiguous_ctx = make_aarch64_ctx();
        ambiguous_ctx.symbols = std::rc::Rc::clone(&exact_ctx.symbols);
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
            CExpr::deref(ambiguous_ctx.name_ref("fp_a")),
            vec![CExpr::IntLit(1)],
        );
        let unresolved_observed = CExpr::call(
            CExpr::deref(ambiguous_ctx.name_ref("fp_b")),
            vec![CExpr::IntLit(1)],
        );
        let mut unresolved_ctx = make_aarch64_ctx();
        unresolved_ctx.symbols = std::rc::Rc::clone(&exact_ctx.symbols);
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
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&eax.display_name(), crate::analysis::SemanticValue::Load {
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
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&load_first.display_name(), crate::analysis::SemanticValue::Load {
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
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&load_second.display_name(), crate::analysis::SemanticValue::Load {
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&ret.display_name(), CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref(&load_first.display_name()),
                ctx.name_ref(&load_second.display_name()),
            ),
        );

        let expr = ctx.get_return_expr(&ret);
        let rendered = spelled(&ctx, &expr);
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
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&ret.display_name(), crate::analysis::SemanticValue::Load {
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
        let rendered = spelled(&ctx, &expr);
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent("ecx", CExpr::binary(
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
    fn scalar_context_visible_expr_ranking_prefers_scalar_candidates_over_stack_artifacts() {
        let mut ctx = make_x86_64_ctx();
        ctx.state.analysis_ctx.use_info.insert_stack_slot_for_name(&"var_8h".to_string(), crate::analysis::StackSlotProvenance {
                offset: -8,
                predicate_carrier: true,
                return_carrier: false,
                value_kind: crate::analysis::StackSlotValueKind::Scalar,
            },
        );
        ctx.state.analysis_ctx.use_info.insert_stack_slot_for_name(&"var_ch".to_string(), crate::analysis::StackSlotProvenance {
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
        ctx.state.analysis_ctx.use_info.insert_stack_slot_for_name(&"tmp:11f00_1".to_string(), crate::analysis::StackSlotProvenance {
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
                symbols: ctx.inputs.binary_symbols,
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
        ctx.inputs.binary_symbols = Box::leak(Box::new(symbols));
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
            CExpr::External { name: "sym.imp.fact_helper".to_string(), kind: crate::symbol::ExternalKind::Import }
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

        let CStmt::Expr(CExpr::Call { func, args, .. }) = stmt else {
            panic!("expected certified call expression, got {stmt:?}");
        };
        assert_eq!(
            *func,
            CExpr::External {
                name: "sym.helper".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            }
        );
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

        let CStmt::Expr(CExpr::Call { func, args, .. }) = stmt else {
            panic!("expected certified call expression, got {stmt:?}");
        };
        assert_eq!(
            *func,
            CExpr::External {
                name: "sym.helper".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            }
        );
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
            Some(CExpr::call_at((0x1000, 2), 
                CExpr::External {
                    name: "sym.helper".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                },
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
        // The view was built before this context, so it adopts the view's table.
        uncertified_alias_ctx.symbols = std::rc::Rc::new(std::cell::RefCell::new(symbols.borrow().clone()));
        uncertified_alias_ctx
            .state.analysis_ctx.use_info.insert_call_result_source_alias(&"alias".to_string(), source_call);
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
        certified_alias_ctx.symbols = std::rc::Rc::new(std::cell::RefCell::new(symbols.borrow().clone()));
        certified_alias_ctx.inputs.visible_bindings =
            Box::leak(Box::new(vec![visible_stack_binding(
                "alias",
                Some(CType::Int(32)),
                8,
            )]));
        certified_alias_ctx
            .state.analysis_ctx.use_info.insert_call_result_source_alias(&"alias".to_string(), source_call);
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

        let CStmt::Expr(CExpr::Call { func, args, .. }) = stmt else {
            panic!("expected certified zero-arg call, got {stmt:?}");
        };
        assert_eq!(
            *func,
            CExpr::External {
                name: "sym.helper".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            }
        );
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
            &CExpr::External { name: "sym.helper".to_string(), kind: crate::symbol::ExternalKind::Function },
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent("tmp:ret_1", CExpr::binary(
                BinaryOp::BitXor,
                ctx.name_ref("value"),
                CExpr::IntLit(1),
            ),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .insert_definition_for_name_if_absent("const:1_0", CExpr::IntLit(1));

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
            .insert_definition_for_name_if_absent("tmp:3e480_1", CExpr::IntLit(7));

        assert_eq!(
            unmapped.expand_return_expr(
                &unmapped.name_ref("value_3e480"),
                0,
                &mut HashSet::new()
            ),
            unmapped.name_ref("value_3e480")
        );
        assert_eq!(
            unmapped.expand_return_expr(&unmapped.name_ref("t42_1"), 0, &mut HashSet::new()),
            unmapped.name_ref("t42_1")
        );
        unmapped
            .state
            .analysis_ctx
            .use_info
            .insert_definition_for_name_if_absent("ordinary_alias", CExpr::IntLit(9));
        assert_eq!(
            unmapped.expand_return_expr(
                &unmapped.name_ref("ordinary_alias"),
                0,
                &mut HashSet::new()
            ),
            unmapped.name_ref("ordinary_alias")
        );

        let mut mapped = make_x86_64_ctx();
        mapped
            .state
            .analysis_ctx
            .use_info
            .insert_definition_for_name_if_absent("tmp:3e480_1", CExpr::IntLit(7));
        mapped
            .state
            .analysis_ctx
            .use_info
            .var_aliases
            .insert("tmp:3e480_1".to_string(), "value_3e480".to_string());

        assert_eq!(
            mapped.expand_return_expr(
                &mapped.name_ref("value_3e480"),
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
            .insert_definition_for_name_if_absent(&source.display_name(), ctx.name_ref("stack_slot"));

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
        // Each case renders in its own context, so its names are declared there.
        let cases = ["src_transient", "src_stack_placeholder", "src_low_quality"];
        let spellings = ["rax_7", "stack", "value_bad"];

        for (source_name, spelling) in cases.into_iter().zip(spellings) {
            let mut ctx = make_x86_64_ctx();
            let bad_expr = ctx.name_ref(spelling);
            let source = make_var(source_name, 1, 8);
            ctx.state
                .analysis_ctx
                .use_info
                .insert_definition_for_name_if_absent(&source.display_name(), bad_expr);

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
        // Each case renders in its own context, so its names are declared there.
        let cases = ["src_transient", "src_stack_placeholder", "src_low_quality"];
        let spellings = ["rax_7", "stack", "value_bad"];

        for (source_name, spelling) in cases.into_iter().zip(spellings) {
            let mut ctx = make_x86_64_ctx();
            let bad_expr = ctx.name_ref(spelling);
            let source = make_var(source_name, 1, 8);
            ctx.state
                .analysis_ctx
                .use_info
                .insert_definition_for_name_if_absent(&source.display_name(), bad_expr);
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
            .insert_definition_for_name_if_absent(&source.display_name(), ctx.name_ref("rax_7"));
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
            .insert_definition_for_name_if_absent(&source.display_name(), ctx.name_ref("buf"));
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
            .insert_definition_for_name_if_absent(&source.display_name(), stable_source.clone());
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
        ctx.inputs.binary_symbols = Box::leak(Box::new(HashMap::from([(
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&slot.display_name(), CExpr::binary(
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&slot.display_name(), CExpr::binary(
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&stored_slot.display_name(), CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(-8),
            ),
        );
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&loaded_slot.display_name(), CExpr::binary(
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&slot.display_name(), CExpr::binary(
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

        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&addr.display_name(), CExpr::binary(
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&addr.display_name(), CExpr::binary(
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
                    ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&store_val.to_string(), source_call);
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
                    ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&store_val.to_ascii_lowercase(), source_call);
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
                        .insert_call_result_source_alias(&store_val.to_string(), (source_call.0, source_call.1 + 1));
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
                        .insert_call_result_source_alias(
                            &store_val.to_ascii_lowercase(),
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
        ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&store_val.clone(), source_call);

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
