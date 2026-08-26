#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        collections::{BTreeMap, BTreeSet, HashMap, HashSet},
        ops::Deref,
        rc::Rc,
        sync::Arc,
    };

    use crate::analysis::PtrArith;

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

    use crate::fold::context::{EffectOccurrenceKind, empty_function_facts};
    use crate::{
        FoldArchConfig, FoldInputs,
        analysis::{
            CallOwner, CallOwnerKind, CallOwnershipFact, CallSiteId, PreparedSemanticView,
            StackSlotProvenance, StackSlotValueKind,
        },
        ast::{CFunction, CLocal},
    };
    use crate::analysis::ownership::CallOwnerIdentity;
    use r2il::{
        ArchSpec, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef, RegisterProjection,
        RegisterProjectionDisposition, RegisterStorage, SpaceId, Varnode,
    };
    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }

    fn test_symbol(ctx: &FoldingContext<'_>, name: &str) -> crate::symbol::SymbolId {
        let CExpr::Var(symbol) = ctx.name_ref(name) else {
            unreachable!("fixture variable must be a symbol")
        };
        symbol
    }

    fn install_test_param_aliases(
        ctx: &mut FoldingContext<'_>,
        aliases: HashMap<String, String>,
    ) {
        let mut view = ctx
            .inputs
            .prepared_semantic_view
            .cloned()
            .unwrap_or_default();
        view.param_alias_by_reg = aliases;
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(view)));
    }
    use r2types::{
        CalleeFact, CalleeReturnRelation, ExternalField, ExternalStackBase, ExternalStackVarSpec,
        ExternalStruct, ExternalTypeDb, Signedness, SolvedTypes, SolverDiagnostics, StackSlotKey,
        StructShape, TypeArena, TypeId, TypeOracle, VisibleBinding, VisibleBindingKind,
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

    fn install_callsite_resolution(
        ctx: &mut FoldingContext<'_>,
        source_call: (u64, usize),
        target_addr: u64,
        target_name: &str,
        signature: Option<FunctionType>,
    ) {
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

    fn install_call_owner(
        ctx: &mut FoldingContext<'_>,
        source_call: (u64, usize),
        owner_name: &str,
        alias: &str,
    ) {
        let source_id = CallSiteId::from(source_call);
        let owner_value = ctx
            .state
            .analysis_ctx
            .use_info
            .value_id_for_name_or_bind(owner_name)
            .expect("fixture owner must have one exact value");
        let alias_value = ctx
            .state
            .analysis_ctx
            .use_info
            .value_id_for_name_or_bind(alias)
            .expect("fixture alias must have one exact value");
        ctx.state.analysis_ctx.ownership.call_ownership.insert(
            source_id,
            CallOwnershipFact {
                source: source_id,
                owner: Some(CallOwner {
                    identity: CallOwnerIdentity::Value(owner_value),
                    kind: CallOwnerKind::StableLocal,
                }),
                aliases: BTreeSet::from([alias_value]),
                direct_aliases: BTreeSet::from([alias_value]),
            },
        );
        ctx.state
            .analysis_ctx
            .ownership
            .value_sources
            .insert(alias_value, source_id);
        ctx.state
            .analysis_ctx
            .use_info
            .insert_call_result_source_for_value(alias_value, source_call);
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
        FoldingContext::from_inputs(FoldInputs {
            normalization_origins: None,
            observation_journal: None,
            binding_names: None,
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
        FoldingContext::from_inputs(FoldInputs {
            normalization_origins: None,
            observation_journal: None,
            binding_names: None,
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
        ctx.inputs.normalization_origins = Some(Box::leak(Box::new(
            crate::normalize::NormalizationOrigins::for_unchanged(
                prepared_ssa.function(),
                prepared_ssa,
            ),
        )));
        ctx
    }

    fn make_aarch64_ctx_with_prepared<'a>(
        prepared_ssa: &'a SourceOwnedPreparedFixture,
    ) -> FoldingContext<'a> {
        let mut ctx = make_aarch64_ctx();
        ctx.inputs.prepared_ssa = Some(prepared_ssa);
        ctx.inputs.function_facts = prepared_ssa.function_facts();
        ctx.inputs.normalization_origins = Some(Box::leak(Box::new(
            crate::normalize::NormalizationOrigins::for_unchanged(
                prepared_ssa.function(),
                prepared_ssa,
            ),
        )));
        ctx
    }

    fn install_observed_lowering<'a>(
        ctx: &mut FoldingContext<'a>,
        prepared: &SourceOwnedPreparedFixture,
    ) -> (
        Rc<crate::binding_plan::BindingPlan>,
        &'static Rc<crate::binding_plan::BindingNameResolution>,
        &'static std::cell::RefCell<crate::observation_journal::LegacyObservationJournal>,
    ) {
        let plan = Rc::new(
            crate::binding_plan::BindingPlan::build_shadow(&prepared.facts)
                .expect("observed lowering binding plan"),
        );
        let names = Box::leak(Box::new(Rc::new(
            crate::binding_plan::BindingNameResolution::build(
                &prepared.facts,
                Rc::clone(&plan),
                Rc::clone(&ctx.symbols),
            )
            .expect("observed lowering binding names"),
        )));
        let origins = ctx
            .inputs
            .normalization_origins
            .expect("prepared observed lowering origins");
        let journal = Box::leak(Box::new(std::cell::RefCell::new(
            crate::observation_journal::LegacyObservationJournal::new(
                &prepared.facts,
                prepared.function(),
                origins,
                Rc::clone(&plan),
                Rc::clone(&ctx.symbols),
            )
            .expect("observed lowering journal"),
        )));
        ctx.inputs.binding_names = Some(names);
        ctx.inputs.observation_journal = Some(journal);
        (plan, names, journal)
    }

    fn seal_observed_lowering(
        prepared: &SourceOwnedPreparedFixture,
        plan: Rc<crate::binding_plan::BindingPlan>,
        names: &Rc<crate::binding_plan::BindingNameResolution>,
        journal: &std::cell::RefCell<crate::observation_journal::LegacyObservationJournal>,
        symbols: Rc<std::cell::RefCell<crate::symbol::SymbolTable>>,
        ret_type: CType,
        body: Vec<CStmt>,
    ) -> crate::observation_journal::SealedNativeFunction {
        let origins =
            crate::normalize::NormalizationOrigins::for_unchanged(prepared.function(), prepared);
        let replacement = crate::observation_journal::LegacyObservationJournal::new(
            &prepared.facts,
            prepared.function(),
            &origins,
            Rc::clone(&plan),
            Rc::clone(&symbols),
        )
        .expect("replacement journal for owned extraction");
        let journal = journal.replace(replacement);
        let mut function = CFunction::new("observed_lowering", ret_type);
        function.symbols = symbols;
        function.locals = plan
            .bindings()
            .map(|(binding, fact)| CLocal {
                ty: fact.declaration_type().clone(),
                name: names
                    .symbol_for_binding(binding)
                    .expect("dense observed binding name"),
                stack_offset: None,
            })
            .collect();
        function.body = body;
        crate::observation_journal::MarkedNativeDraft::new(function, journal)
            .seal(&prepared.facts)
            .expect("observed lowering must seal")
    }

    fn exact_legacy_use(
        plan: &crate::binding_plan::BindingPlan,
        site: r2ssa::UseSite,
    ) -> crate::shadow_report::LegacyUseObservation {
        match plan.use_disposition(site) {
            Some(r2ssa::MachineUseDisposition::Exact(slice)) => {
                crate::shadow_report::LegacyUseObservation::Exact(*slice)
            }
            Some(r2ssa::MachineUseDisposition::MemoryAddress(address)) => {
                crate::shadow_report::LegacyUseObservation::MemoryAddress(*address)
            }
            other => panic!("expected exact machine use at {site:?}, got {other:?}"),
        }
    }

    fn exact_legacy_write(
        plan: &crate::binding_plan::BindingPlan,
        inst: r2ssa::InstId,
    ) -> crate::shadow_report::LegacyWriteObservation {
        match plan.write_disposition(inst) {
            Some(r2ssa::MachineWriteDisposition::Exact(write)) => {
                crate::shadow_report::LegacyWriteObservation::Exact(*write)
            }
            other => panic!("expected exact machine write at {inst:?}, got {other:?}"),
        }
    }

    #[test]
    fn observed_inline_repeated_equal_operands_keep_distinct_use_sites_and_output() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(5, 8),
        });
        entry.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::unique(0x10, 8),
            b: Varnode::unique(0x10, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("observed_repeated_equal_operands");
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let op_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::IntAdd { .. }))
            .expect("integer addition");
        let inst = prepared
            .graph()
            .inst_id_for_op_site(block.addr, op_idx)
            .expect("addition graph instruction");
        let graph_inst = prepared.graph().inst(inst).expect("addition graph row");
        assert_eq!(graph_inst.inputs.len(), 2);
        assert_eq!(graph_inst.inputs[0], graph_inst.inputs[1]);
        let left = r2ssa::UseSite { inst, input_idx: 0 };
        let right = r2ssa::UseSite { inst, input_idx: 1 };

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (plan, names, journal) = install_observed_lowering(&mut ctx, &prepared);
        let LoweredExprAt::Rendered(expr) =
            ctx.op_to_expr_at(&block.ops[op_idx], block.addr, op_idx)
                .expect("integer addition lowering");
        let CExpr::Binary { left: lhs, right: rhs, .. } = expr.unobserved() else {
            panic!("integer addition must retain its binary operand positions");
        };
        let input_value = graph_inst.inputs[0];
        let input_symbol = names
            .symbol_for_value(input_value)
            .expect("bound input symbol");
        assert!(
            matches!(lhs.as_ref(), CExpr::Observed { .. }),
            "left input observations must stay on the left occurrence"
        );
        assert!(
            matches!(rhs.as_ref(), CExpr::Observed { .. }),
            "right input observations must stay on the right occurrence"
        );
        let is_exact_projected_binding = |expr: &CExpr| {
            matches!(
                expr.unobserved(),
                CExpr::Cast {
                    ty: CType::UInt(64),
                    expr,
                } if matches!(expr.unobserved(), CExpr::Var(symbol) if *symbol == input_symbol)
            )
        };
        assert!(
            is_exact_projected_binding(lhs),
            "the exact bound value must render through its planned symbol and use width"
        );
        assert!(
            is_exact_projected_binding(rhs),
            "equal operands must independently project the same planned binding"
        );
        assert_eq!(*ctx.observation_error.borrow(), None);
        let symbols = Rc::clone(&ctx.symbols);
        drop(ctx);
        let sealed = seal_observed_lowering(
            &prepared,
            Rc::clone(&plan),
            names,
            journal,
            symbols,
            CType::UInt(64),
            vec![CStmt::Return(Some(expr))],
        );

        assert_eq!(
            sealed.observations().use_observation(left),
            Some(exact_legacy_use(&plan, left))
        );
        assert_eq!(
            sealed.observations().use_observation(right),
            Some(exact_legacy_use(&plan, right))
        );
        assert_eq!(
            sealed.observations().write_observation(inst),
            Some(exact_legacy_write(&plan, inst)),
            "the supported expression result must retain its exact output occurrence"
        );
    }

    #[test]
    fn observed_narrow_register_use_projects_the_exact_carrier_slice() {
        let mut arch = make_test_arch_x86_64();
        let mut register_projections = arch
            .registers
            .iter()
            .map(|register| {
                let written = register.storage();
                let carrier = match register.name.as_str() {
                    "EAX" => RegisterStorage { offset: 0, size: 8 },
                    "EDI" => RegisterStorage {
                        offset: 0x10,
                        size: 8,
                    },
                    "ESI" => RegisterStorage {
                        offset: 0x18,
                        size: 8,
                    },
                    _ => written,
                };
                RegisterProjection {
                    written,
                    disposition: RegisterProjectionDisposition::Bound {
                        carrier,
                        slice: RegisterBitSlice {
                            lsb_bit_offset: 0,
                            size_bits: u64::from(register.size) * 8,
                        },
                    },
                }
            })
            .collect::<Vec<_>>();
        register_projections.sort_by_key(|projection| projection.written);
        arch.register_projections = register_projections;
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(0x20, 4),
            src: Varnode::register(0, 4),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("observed_narrow_register_projection");
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let op_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Copy { dst, .. } if dst.name == "tmp:20" && dst.size == 4),
            )
            .expect("narrow register copy");
        let inst = prepared
            .graph()
            .inst_id_for_op_site(block.addr, op_idx)
            .expect("copy graph instruction");
        let graph_inst = prepared.graph().inst(inst).expect("copy graph row");
        let site = r2ssa::UseSite { inst, input_idx: 0 };

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (plan, names, _journal) = install_observed_lowering(&mut ctx, &prepared);
        let slice = match plan.use_disposition(site) {
            Some(r2ssa::MachineUseDisposition::Exact(slice)) => *slice,
            other => panic!("expected exact narrow-register use, got {other:?}"),
        };
        assert_eq!(slice.bit_offset(), 0);
        assert_eq!(slice.width_bits(), 32);
        assert_eq!(
            slice.carrier_width_bits(),
            64,
            "graph input={:?}; storage={:?}",
            prepared.graph().value(graph_inst.inputs[0]),
            prepared
                .graph()
                .value(graph_inst.inputs[0])
                .and_then(|value| value.canonical_storage)
                .and_then(|storage| prepared.machine_context().register_projection(storage))
        );

        let LoweredExprAt::Rendered(expr) =
            ctx.op_to_expr_at(&block.ops[op_idx], block.addr, op_idx)
                .expect("narrow register copy lowering");
        let input_symbol = names
            .symbol_for_value(graph_inst.inputs[0])
            .expect("carrier input symbol");
        assert!(
            matches!(
                expr.unobserved(),
                CExpr::Cast {
                    ty: CType::UInt(32),
                    expr,
                } if matches!(
                    expr.as_ref(),
                    CExpr::Cast {
                        ty: CType::UInt(64),
                        expr,
                    } if matches!(expr.unobserved(), CExpr::Var(symbol) if *symbol == input_symbol)
                )
            ),
            "narrow read must be selected from the unsigned canonical carrier: {expr:?}"
        );
        assert_eq!(*ctx.observation_error.borrow(), None);
    }

    #[test]
    fn observed_narrow_register_write_applies_the_exact_insert_effect() {
        let mut arch = make_test_arch_x86_64();
        let mut register_projections = arch
            .registers
            .iter()
            .map(|register| {
                let written = register.storage();
                let carrier = match register.name.as_str() {
                    "EAX" => RegisterStorage { offset: 0, size: 8 },
                    "EDI" => RegisterStorage {
                        offset: 0x10,
                        size: 8,
                    },
                    "ESI" => RegisterStorage {
                        offset: 0x18,
                        size: 8,
                    },
                    _ => written,
                };
                RegisterProjection {
                    written,
                    disposition: RegisterProjectionDisposition::Bound {
                        carrier,
                        slice: RegisterBitSlice {
                            lsb_bit_offset: 0,
                            size_bits: u64::from(register.size) * 8,
                        },
                    },
                }
            })
            .collect::<Vec<_>>();
        register_projections.sort_by_key(|projection| projection.written);
        arch.register_projections = register_projections;

        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0, 4),
            src: Varnode::constant(0xaa, 4),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("observed_exact_narrow_register_write");
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let copy_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Copy { dst, .. } if dst.size == 4))
            .expect("low-register write");
        let copy_inst = prepared
            .graph()
            .inst_id_for_op_site(block.addr, copy_idx)
            .expect("copy graph instruction");

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (plan, _, _) = install_observed_lowering(&mut ctx, &prepared);
        assert!(matches!(
            plan.write_disposition(copy_inst),
            Some(r2ssa::MachineWriteDisposition::Exact(
                r2ssa::MachineWriteProjection::Insert {
                    bit_offset: 0,
                    width_bits: 32,
                    carrier_width_bits: 64,
                }
            ))
        ));
        let copy_stmt = ctx
            .op_to_stmt_with_args(&block.ops[copy_idx], block.addr, copy_idx)
            .expect("supported copy lowering")
            .expect("low-register assignment");
        let CStmt::Expr(copy_expr) = copy_stmt.unobserved() else {
            panic!("low-register write must remain an assignment");
        };
        let CExpr::Binary {
            op: BinaryOp::Assign,
            right: copy_rhs,
            ..
        } = copy_expr.unobserved()
        else {
            panic!("low-register write must remain an assignment expression");
        };
        assert!(matches!(
            copy_rhs.unobserved(),
            CExpr::Cast {
                ty: CType::UInt(64),
                expr,
            } if matches!(expr.unobserved(), CExpr::Binary { op: BinaryOp::BitOr, .. })
        ));

        assert_eq!(*ctx.observation_error.borrow(), None);
    }

    #[test]
    fn observed_stack_load_keeps_contextual_access_with_an_opaque_base_name() {
        let mut arch = make_test_arch_x86_64();
        arch.registers
            .iter_mut()
            .find(|register| register.offset == 0x20 && register.size == 8)
            .expect("frame-pointer storage")
            .name = "opaque_machine_base".to_string();

        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntSub {
            dst: Varnode::unique(0x100, 8),
            a: Varnode::register(0x20, 8),
            b: Varnode::constant(8, 8),
        });
        entry.push(R2ILOp::Load {
            dst: Varnode::unique(0x200, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        let prepared = prepared_x86_with_stack_slot(
            &[entry],
            &arch,
            r2ssa::StackAddressBase::FramePointer,
            -8,
            4,
        )
        .with_name("observed_contextual_stack_load");
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let load_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Load { .. }))
            .expect("stack load");
        let load_inst = prepared
            .graph()
            .inst_id_for_op_site(block.addr, load_idx)
            .expect("load graph instruction");
        let address_site = r2ssa::UseSite {
            inst: load_inst,
            input_idx: 0,
        };

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (plan, names, _journal) = install_observed_lowering(&mut ctx, &prepared);
        let address = match plan.use_disposition(address_site) {
            Some(r2ssa::MachineUseDisposition::MemoryAddress(address)) => *address,
            other => panic!("expected contextual memory address, got {other:?}"),
        };
        assert_eq!(
            address.memory_access(),
            Some(r2ssa::StructuredAccessId {
                inst: load_inst,
                ordinal: 0,
            })
        );

        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[load_idx], block.addr, load_idx)
            .expect("supported load lowering")
            .expect("structured stack load");
        let CStmt::Expr(assignment) = stmt.unobserved() else {
            panic!("load must remain an assignment: {stmt:?}");
        };
        let CExpr::Binary {
            op: BinaryOp::Assign,
            right,
            ..
        } = assignment.unobserved()
        else {
            panic!("load must retain its assignment expression: {assignment:?}");
        };
        let rendered = spelled(&ctx, right);
        assert!(
            !rendered.contains("opaque_machine_base"),
            "the contextual use must not fall back to its opaque machine binding: {rendered}"
        );
        let address_symbol = names
            .symbol_for_value(address.binding().value())
            .expect("ordinary address binding remains available for non-contextual uses");
        assert!(
            !matches!(right.unobserved(), CExpr::Var(symbol) if *symbol == address_symbol),
            "the load expression must not be replaced by the address value's binding"
        );
        assert_eq!(*ctx.observation_error.borrow(), None);
    }

    #[test]
    fn observed_stack_store_keeps_contextual_target_with_an_opaque_base_name() {
        let mut arch = make_test_arch_x86_64();
        arch.registers
            .iter_mut()
            .find(|register| register.offset == 0x28 && register.size == 8)
            .expect("stack-pointer storage")
            .name = "opaque_store_base".to_string();

        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntSub {
            dst: Varnode::unique(0x300, 8),
            a: Varnode::register(0x28, 8),
            b: Varnode::constant(8, 8),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x300, 8),
            val: Varnode::constant(0x55, 4),
        });
        let prepared = prepared_x86_with_stack_slot(
            &[entry],
            &arch,
            r2ssa::StackAddressBase::StackPointer,
            -8,
            4,
        )
        .with_name("observed_contextual_stack_store");
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let store_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Store { .. }))
            .expect("stack store");
        let store_inst = prepared
            .graph()
            .inst_id_for_op_site(block.addr, store_idx)
            .expect("store graph instruction");
        let address_site = r2ssa::UseSite {
            inst: store_inst,
            input_idx: 0,
        };

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (plan, names, _journal) = install_observed_lowering(&mut ctx, &prepared);
        let address = match plan.use_disposition(address_site) {
            Some(r2ssa::MachineUseDisposition::MemoryAddress(address)) => *address,
            other => panic!("expected contextual store address, got {other:?}"),
        };
        let address_symbol = names
            .symbol_for_value(address.binding().value())
            .expect("ordinary address binding remains available for non-contextual uses");

        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[store_idx], block.addr, store_idx)
            .expect("supported store lowering")
            .expect("structured stack store");
        let CStmt::Expr(assignment) = stmt.unobserved() else {
            panic!("store must remain an assignment: {stmt:?}");
        };
        let CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            ..
        } = assignment.unobserved()
        else {
            panic!("store must retain its assignment expression: {assignment:?}");
        };
        let rendered = spelled(&ctx, left);
        assert!(
            !rendered.contains("opaque_store_base"),
            "the contextual store must not fall back to its opaque machine binding: {rendered}"
        );
        assert!(
            !matches!(left.unobserved(), CExpr::Var(symbol) if *symbol == address_symbol),
            "the store target must not be replaced by the address value's binding"
        );
        assert_eq!(*ctx.observation_error.borrow(), None);
    }

    fn assert_observed_call_marks_only_graph_target(indirect: bool) {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x10, 8),
            src: Varnode::constant(7, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(0x401050, 8),
        });
        let target = Varnode::unique(0x10, 8);
        if indirect {
            entry.push(R2ILOp::CallInd { target });
        } else {
            entry.push(R2ILOp::Call { target });
        }
        let prepared = prepared_from_r2il_blocks(&[entry], &arch).with_name(if indirect {
            "observed_indirect_call_target"
        } else {
            "observed_direct_call_target"
        });
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let op_idx = block
            .ops
            .iter()
            .position(|op| {
                if indirect {
                    matches!(op, SSAOp::CallInd { .. })
                } else {
                    matches!(op, SSAOp::Call { .. })
                }
            })
            .expect("call operation");
        let inst = prepared
            .graph()
            .inst_id_for_op_site(block.addr, op_idx)
            .expect("call graph instruction");
        let graph_inst = prepared.graph().inst(inst).expect("call graph row");
        assert_eq!(
            graph_inst.inputs.len(),
            1,
            "semantic call arguments must not become graph inputs"
        );
        let target_site = r2ssa::UseSite { inst, input_idx: 0 };

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_certified_function_facts(&mut ctx);
        let (plan, names, journal) = install_observed_lowering(&mut ctx, &prepared);
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[op_idx], block.addr, op_idx)
            .expect("supported call lowering")
            .expect("certified call statement");
        let CStmt::Expr(call) = stmt.unobserved() else {
            panic!("expected call expression, got {stmt:?}");
        };
        let CExpr::Call { args, .. } = call.unobserved() else {
            panic!("expected call expression, got {call:?}");
        };
        assert!(
            !args.is_empty(),
            "fixture must render at least one semantic argument"
        );
        assert_eq!(*ctx.observation_error.borrow(), None);
        let symbols = Rc::clone(&ctx.symbols);
        drop(ctx);
        let sealed = seal_observed_lowering(
            &prepared,
            Rc::clone(&plan),
            names,
            journal,
            symbols,
            CType::Void,
            vec![stmt],
        );

        assert_eq!(
            sealed.observations().use_observation(target_site),
            Some(exact_legacy_use(&plan, target_site))
        );
        assert_eq!(
            sealed
                .observations()
                .use_observation(r2ssa::UseSite { inst, input_idx: 1 }),
            None,
            "rendered semantic arguments are not SSA graph uses of the call"
        );
    }

    #[test]
    fn observed_direct_call_marks_only_graph_target_input() {
        assert_observed_call_marks_only_graph_target(false);
    }

    #[test]
    fn observed_indirect_call_marks_only_graph_target_input() {
        assert_observed_call_marks_only_graph_target(true);
    }

    #[test]
    fn observed_statement_lowering_preserves_the_direct_finalized_statement() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(0x20, 8),
            src: Varnode::constant(7, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("observed_finalized_statement_once");
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let op_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Copy { .. }))
            .expect("copy operation");

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let _observations = install_observed_lowering(&mut ctx, &prepared);
        let frame = LowerFrame::for_stmt(
            ctx.normalized_site(block.addr, op_idx),
            Some((block.addr, op_idx)),
            true,
        );
        let direct = ctx
            .op_to_stmt_impl(&block.ops[op_idx], &frame)
            .expect("supported direct lowering")
            .expect("direct finalized statement");
        let lowered = ctx
            .op_to_stmt_with_args(&block.ops[op_idx], block.addr, op_idx)
            .expect("supported public lowering")
            .expect("public statement lowering");

        assert_eq!(
            direct.clone_without_render_observations(),
            lowered.clone_without_render_observations(),
            "statement lowering must attach output identity without re-running assignment finalization",
        );
    }

    #[test]
    fn unsupported_expression_is_typed_refusal_before_ast_lowering() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntCarry {
            dst: Varnode::unique(0x20, 1),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(1, 8),
        });
        let prepared =
            prepared_from_r2il_blocks(&[entry], &arch).with_name("unsupported_expression_fallback");
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let op_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::IntCarry { .. }))
            .expect("unsupported carry operation");
        let inst = prepared
            .graph()
            .inst_id_for_op_site(block.addr, op_idx)
            .expect("carry graph instruction");
        assert!(
            prepared
                .graph()
                .inst(inst)
                .and_then(|row| row.output)
                .is_some(),
            "fixture must have a genuine graph output"
        );

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (plan, _, _) = install_observed_lowering(&mut ctx, &prepared);
        assert!(
            matches!(
                plan.write_disposition(inst),
                Some(r2ssa::MachineWriteDisposition::Exact(_))
            ),
            "absence is meaningful only for an exact upstream write"
        );
        assert_eq!(
            ctx.op_to_expr_at(&block.ops[op_idx], block.addr, op_idx),
            Err(OpLoweringRefusal::UnrepresentableOperation),
            "an expression-required renderer gap must not manufacture its destination"
        );
        assert_eq!(*ctx.observation_error.borrow(), None);
    }

    #[test]
    fn opaque_pipeline_refusal_retains_the_upstream_machine_failures() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CallOther {
            output: Some(Varnode::unique(0x20, 8)),
            userop: 7,
            inputs: vec![Varnode::register(0x10, 8)],
        });
        entry.push(R2ILOp::CpuId {
            dst: Varnode::unique(0x28, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch).with_name("opaque_pipeline");
        let plan = crate::binding_plan::BindingPlan::build_shadow(&prepared.facts)
            .expect("partial binding plan retains upstream refusal cells");
        let failures = plan.machine_projection().failures();

        assert!(failures.iter().any(|failure| {
            matches!(
                failure.error(),
                r2ssa::MachineBuildError::UnsupportedOperation { op, .. }
                    if matches!(op.as_ref(), SSAOp::CallOther { .. })
            )
        }));
        assert!(failures.iter().any(|failure| {
            matches!(
                failure.error(),
                r2ssa::MachineBuildError::UnsupportedOperation { op, .. }
                    if matches!(op.as_ref(), SSAOp::CpuId { .. })
            )
        }));

        let input = crate::DecompilerInput::new(prepared.facts.clone());
        let audit = crate::Decompiler::new(crate::DecompilerConfig::x86_64())
            .decompile_input_with_binding_audit(&input);
        assert!(matches!(
            audit.binding_shadow(),
            crate::BindingShadowAuditOutcome::Failed(_)
        ));
        let effects = audit.effect_obligations();
        assert_eq!(
            effects.disposition,
            crate::EffectObligationDisposition::Refused
        );
        assert_eq!(effects.total, 2);
        assert_eq!(effects.rendered, 0);
        assert_eq!(effects.justified_elision, 0);
        assert_eq!(effects.refused, 2);
        assert_eq!(effects.unaccounted, 0);
        assert_eq!(effects.conflicts, 0);
        assert_eq!(
            audit.render_refusal(),
            None,
            "the production path must stop on the upstream machine failure before defensive renderer classification"
        );
        assert!(
            !audit.output().contains("callother(") && !audit.output().contains("CPUID"),
            "opaque operations must not survive as executable helper-shaped C: {}",
            audit.output()
        );
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
            ctx.name_ref("local_3"));
        let cross_slot_rhs = ctx.rewrite_scalar_stack_placeholder_rhs(
            &ctx.name_ref("sum"),
            ctx.name_ref("local_17"));

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

    fn expr_contains_var(ctx: &FoldingContext<'_>, expr: &CExpr, target: &str) -> bool {
        match expr {
            CExpr::Observed { expr, .. } => expr_contains_var(ctx, expr, target),
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
            CExpr::Observed { expr, .. } => expr_contains_addr_of(expr),
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

    #[test]
    fn test_constant_parsing() {
        assert_eq!(parse_const_value("const:0x42"), Some(0x42));
        assert_eq!(parse_const_value("const:42"), Some(0x42));
        assert_eq!(parse_const_value("const:0d42"), Some(42));
        assert_eq!(parse_const_value("const:fffffffc"), Some(0xfffffffc));
        assert_eq!(parse_const_value("const:0x42_0"), Some(0x42));
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
    fn modeled_call_target_uses_typed_resolution_without_fact_scan() {
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
            }, &super::LowerFrame::for_expr(),
            )
            .expect("supported indirect-call lowering")
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
    fn indirect_callable_classification_is_observation_transparent() {
        let ctx = FoldingContext::new(64);
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (target_id, target) = owner
            .observe_expr(ctx.name_ref("callback"))
            .expect("target observation");
        let callable = FoldingContext::indirect_callable_expr(target);
        let mut function = CFunction::new("invoke", CType::Void)
            .with_body(vec![CStmt::Expr(callable)]);

        let reachable = crate::ast::strip_render_observations(
            &mut function,
            owner.expected_count())
        .expect("target marker must survive exactly once");

        assert!(reachable.contains(target_id));
        assert_eq!(
            function.body,
            vec![CStmt::Expr(ctx.name_ref("callback"))],
            "a marker around an already-callable variable must not invent a dereference"
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
            .expect("supported call lowering")
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
            .expect("supported indirect-call lowering")
            .expect("indirect call-with-args fallback statement");

        assert!(
            matches!(&stmt, CStmt::Comment(comment) if comment.contains("uncertified indirect-call arguments")),
            "typed callee identity alone must not authorize executable indirect call-with-args output: {stmt:?}",
        );
    }

    #[test]
    fn predicate_owner_rewrite_rejects_generic_argument_owner() {
        let mut ctx = make_x86_64_ctx();
        install_call_owner(&mut ctx, (0x1000, 2), "arg1", "rax_1");

        let predicate = CExpr::binary(
            BinaryOp::Eq,
            ctx.name_ref("rax_1"),
            CExpr::IntLit(0));

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
            CExpr::IntLit(0));

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
                vec![ctx.name_ref("rax_1")]),
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
            CExpr::IntLit(0));

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
            CExpr::IntLit(0));

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
                CExpr::IntLit(0));

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
install_test_param_aliases(&mut ctx, HashMap::from([(
            "x1".to_string(),
            "argv".to_string(),
        )]));

        let expr = CExpr::binary(
            BinaryOp::Add,
            ctx.name_ref("argv"),
            CExpr::IntLit(8));
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
        let ctx = FoldingContext::new(64);

        let expr = ctx.identity_simplify_binary(
            BinaryOp::Add,
            ctx.name_ref("b"),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("a"),
                CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("a"),
                    ctx.name_ref("a")),
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
        let ctx = FoldingContext::new(64);

        let expr = ctx.identity_simplify_binary(
            BinaryOp::Add,
            ctx.name_ref("buf"),
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("i"),
                ctx.name_ref("i")),
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

        let callee = CExpr::External { name: "sym.helper".to_string(), kind: crate::symbol::ExternalKind::Function,
        };
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
    fn expr_type_hint_preserves_cast_through_paren() {
        let ctx = make_x86_64_ctx();

        assert_eq!(
            ctx.expr_type_hint(&CExpr::cast(
                CType::Int(16),
                ctx.name_ref("value")
            )),
            Some(CType::Int(16))
        );
        assert_eq!(
            ctx.expr_type_hint(&CExpr::Paren(Box::new(CExpr::cast(
                CType::Int(16),
                ctx.name_ref("value"),
            )))),
            Some(CType::Int(16))
        );
    }

    #[test]
    fn test_arm64_registers_are_treated_as_register_like_artifacts() {
        let ctx = FoldingContext::new(64);
        assert!(ctx.inputs.arch.is_register_like_base_name("x8"));
        assert!(ctx.inputs.arch.is_register_like_base_name("w9"));
        assert!(ctx.inputs.arch.is_register_like_base_name("x30"));

        let carrier = CStmt::Expr(CExpr::assign(
            ctx.name_ref("x8_9"),
            CExpr::IntLit(1)));
        assert!(ctx.stmt_is_side_effect_free_versioned_register_carrier(&carrier));

        let local = CStmt::Expr(CExpr::assign(
            ctx.name_ref("var_8h"),
            CExpr::IntLit(1)));
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
            Ok(ctx.name_ref("ram:401000"))
        );
        assert_eq!(
            ctx.get_expr(&make_var("const:402000", 0, 8)),
            Ok(CExpr::IntLit(0x402000))
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
            .expect("supported copy lowering")
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
    fn should_inline_and_reads_require_the_exact_sealed_disposition() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(7, 8),
        });
        entry.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::unique(0x10, 8),
            b: Varnode::constant(1, 8),
        });
        entry.push(R2ILOp::CallOther {
            output: Some(Varnode::unique(0x30, 8)),
            userop: 7,
            inputs: Vec::new(),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("sealed_inline_admission");
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let SSAOp::Copy { dst, src } = &block.ops[0] else {
            panic!("fixture must begin with a copy");
        };
        let refused = block
            .ops
            .iter()
            .find_map(|op| match op {
                SSAOp::CallOther {
                    output: Some(output),
                    ..
                } => Some(output),
                _ => None,
            })
            .expect("refused output value");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (plan, names, _) = install_observed_lowering(&mut ctx, &prepared);
        let src_value = prepared
            .graph()
            .value_id_for_var(src)
            .expect("constant source value");
        let dst_value = prepared
            .graph()
            .value_id_for_var(dst)
            .expect("copy destination value");
        let refused_value = prepared
            .graph()
            .value_id_for_var(refused)
            .expect("refused output identity");

        assert!(matches!(
            plan.disposition(src_value),
            Some(crate::binding_plan::ValueDisposition::Inline { .. })
        ));
        assert!(ctx.should_inline(src));
        assert!(!matches!(
            plan.disposition(dst_value),
            Some(crate::binding_plan::ValueDisposition::Inline { .. })
        ));
        assert!(!ctx.should_inline(dst));
        assert!(matches!(
            plan.disposition(refused_value),
            Some(crate::binding_plan::ValueDisposition::Refused { .. })
        ));
        assert!(!ctx.should_inline(refused));

        ctx.inlined_renderings
            .borrow_mut()
            .insert(src.display_name(), CExpr::IntLit(99));
        ctx.inlined_renderings
            .borrow_mut()
            .insert(dst.display_name(), CExpr::IntLit(100));
        ctx.inlined_renderings
            .borrow_mut()
            .insert(refused.display_name(), CExpr::IntLit(101));
        assert_eq!(ctx.get_expr(src), Ok(CExpr::IntLit(7)));
        assert_eq!(
            ctx.get_expr(dst),
            Ok(CExpr::Var(
                names
                    .symbol_for_value(dst_value)
                    .expect("bound destination symbol")
            ))
        );
        assert_eq!(
            ctx.get_expr(refused),
            Err(OpLoweringRefusal::MissingProgramVariableAuthorization)
        );
    }

    #[test]
    fn test_get_return_expr_semanticizes_raw_member_derefs_from_typed_base() {
        let base = make_var("arg1", 0, 8);
        let ret = make_var("tmp:9300", 1, 8);
        let mut ctx = FoldingContext::new(64);
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

        let expr = ctx
            .get_return_expr(&ret)
            .expect("fixture return expression should lower");
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
        install_test_param_aliases(&mut ctx,
            [("rdi".to_string(), "arg1".to_string())]
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

        let expr = ctx
            .get_return_expr(&ret)
            .expect("fixture return expression should lower");
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
                    CExpr::IntLit(4)),
            ),
        );
        ctx.state
            .analysis_ctx
            .use_info
            .insert_definition_for_name_if_absent(&real_index.display_name(), ctx.name_ref("local_c"),
            );
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&real_index.display_name(), crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Expr(CExpr::Var(
                { let CExpr::Var(id) = ctx.name_ref("local_c") else { unreachable!() }; id }),
                )),
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
        };

        assert!(matches!(render(SpaceId::Ram), Some(CExpr::Deref(_))));
        assert_eq!(
            render(SpaceId::Custom(7)),
            None,
            "the advisory semantic cache cannot authorize executable non-RAM loads"
        );
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
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&len_value.display_name(), crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Expr(CExpr::Var(
                { let CExpr::Var(id) = ctx.name_ref("len") else { unreachable!() }; id }),
                )),
        );
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&buf_value.display_name(), crate::analysis::SemanticValue::Scalar(crate::analysis::ScalarValue::Expr(CExpr::Var(
                { let CExpr::Var(id) = ctx.name_ref("buf") else { unreachable!() }; id }),
                )),
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
                    CExpr::IntLit(56)),
            ),
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&addr.display_name(), CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("arg1"),
                CExpr::binary(
                    BinaryOp::Shl,
                    ctx.name_ref("arg2"),
                    CExpr::IntLit(2)),
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&addr.display_name(), CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("i"),
                ctx.name_ref("buf")),
        );

        let direct = ctx
            .indexed_pointer_add_expr(
                &CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("i"),
                    ctx.name_ref("buf")),
                &CType::u8(),
            )
            .expect("typed commuted pointer add should normalize directly");
        assert!(matches!(direct, CExpr::Subscript { .. }), "{direct:?}");

        let expr = ctx
            .render_canonical_load_expr(&dst, &addr, CType::u8())
            .expect("typed load should lower");
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
        let arch = make_test_arch_x86_64();
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
        )
        .with_context(r2types::ParsedExternalContext {
            stack_slots: BTreeMap::from([
                (
                    StackSlotKey {
                        base: ExternalStackBase::FramePointer,
                        offset: -4,
                    },
                    r2types::ExternalStackSlotSpec {
                        name: "first_slot".to_string(),
                        ty: Some(r2types::CTypeLike::Int {
                            bits: 32,
                            signedness: r2types::Signedness::Signed,
                        }),
                        base: ExternalStackBase::FramePointer,
                        role: r2types::ExternalStackSlotRole::Local,
                        ..r2types::ExternalStackSlotSpec::default()
                    },
                ),
                (
                    StackSlotKey {
                        base: ExternalStackBase::FramePointer,
                        offset: -8,
                    },
                    r2types::ExternalStackSlotSpec {
                        name: "second_slot".to_string(),
                        ty: Some(r2types::CTypeLike::Int {
                            bits: 32,
                            signedness: r2types::Signedness::Signed,
                        }),
                        base: ExternalStackBase::FramePointer,
                        role: r2types::ExternalStackSlotRole::Local,
                        ..r2types::ExternalStackSlotSpec::default()
                    },
                ),
            ]),
            ..r2types::ParsedExternalContext::default()
        });
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
        ctx.inputs.visible_bindings = &prepared.function_facts().type_facts().visible_bindings;
        ctx.current_block_addr.set(Some(0x1000));
        ctx.current_op_idx.set(Some(loads[1].0));

        let expr = ctx
            .render_canonical_load_expr(&loads[0].1, &loads[0].2, CType::i32())
            .expect("certified stack load should lower");
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

        let expr = ctx
            .render_canonical_load_expr(&dst, &addr, CType::u64())
            .expect("raw load residual should lower");

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

        let expr = ctx
            .render_canonical_store_target_expr(&addr, 8, CType::u64())
            .expect("raw store target residual should lower");

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
                            CExpr::IntLit(3)),
                        ctx.name_ref("idx"),
                    ),
                    CExpr::IntLit(3),
                ),
            ),
        );
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
        install_test_param_aliases(&mut ctx,
            [
                ("x0".to_string(), "arg1".to_string()),
                ("x1".to_string(), "arg2".to_string()),
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
        install_test_param_aliases(&mut ctx,
            [("x0".to_string(), "obj".to_string())]
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
        install_test_param_aliases(&mut ctx,
            [
                ("x0".to_string(), "arg1".to_string()),
                ("x1".to_string(), "arg2".to_string()),
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
                    CExpr::IntLit(56)),
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
        install_test_param_aliases(&mut ctx,
            [
                ("rdi".to_string(), "items".to_string()),
                ("esi".to_string(), "idx".to_string()),
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
                    CExpr::IntLit(40)),
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
        install_test_param_aliases(&mut ctx,
            [
                ("rdi".to_string(), "arr".to_string()),
                ("esi".to_string(), "idx".to_string()),
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
                    shift_mask.clone()),
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
        install_test_param_aliases(&mut ctx,
            [
                ("rdi".to_string(), "arr".to_string()),
                ("esi".to_string(), "idx".to_string()),
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
                    CExpr::IntLit(56)),
            ),
        );

        let addr = CExpr::binary(
            BinaryOp::Add,
            ctx.name_ref("local_c"),
            CExpr::IntLit(0x34));
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
        install_test_param_aliases(&mut ctx,
            [
                ("x0".to_string(), "arg1".to_string()),
                ("x1".to_string(), "arg2".to_string()),
            ]
            .into_iter()
            .collect(),
        );
        let oracle = FieldNameAnyOnlyOracle;
        ctx.set_type_oracle(Some(&oracle));

        let addr = CExpr::binary(
            BinaryOp::Add,
            ctx.name_ref("arg1"),
            CExpr::binary(
                BinaryOp::Mul,
                ctx.name_ref("arg2"),
                CExpr::IntLit(4)),
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
                CExpr::IntLit(0xdead)),
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
                ctx.name_ref("y")),
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
            Ok(CExpr::IntLit(-1))
        );
        assert_eq!(
            ctx.get_return_expr(&make_var("const:fffffffe", 0, 4)),
            Ok(CExpr::IntLit(-2))
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
                    CExpr::IntLit(100)),
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
    fn identity_simplification_keeps_only_surviving_occurrence_observations() {
        let ctx = FoldingContext::new(64);
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (value_id, value) = owner
            .observe_expr(ctx.name_ref("x"))
            .expect("value observation");
        let (zero_id, zero) = owner
            .observe_expr(CExpr::IntLit(0))
            .expect("literal observation");
        let (result_id, source) = owner
            .observe_expr(CExpr::binary(BinaryOp::Add, value, zero))
            .expect("result observation");
        let simplified = ctx.simplify_identities(source);
        let mut function = CFunction::new("identity", CType::Int(32))
            .with_body(vec![CStmt::Return(Some(simplified))]);

        let reachable = crate::ast::strip_render_observations(
            &mut function,
            owner.expected_count())
        .expect("surviving identity observations remain well formed");

        assert!(reachable.contains(value_id));
        assert!(reachable.contains(result_id));
        assert!(
            !reachable.contains(zero_id),
            "the eliminated literal must remain unaccounted, not move onto x"
        );
        assert_eq!(
            function.body,
            vec![CStmt::Return(Some(ctx.name_ref("x")))]
        );
    }

    #[test]
    fn linear_identity_rewrite_does_not_guess_a_surviving_operand_occurrence() {
        let ctx = FoldingContext::new(64);
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (first_id, first) = owner
            .observe_expr(ctx.name_ref("x"))
            .expect("first x observation");
        let (second_id, second) = owner
            .observe_expr(ctx.name_ref("x"))
            .expect("second x observation");
        let source = CExpr::binary(
            BinaryOp::Add,
            first,
            CExpr::binary(BinaryOp::Mul, second, CExpr::IntLit(2)),
        );
        let (result_id, source) = owner
            .observe_expr(source)
            .expect("result observation");
        let simplified = ctx.simplify_identities(source);
        let mut function = CFunction::new("linear_identity", CType::Int(32))
            .with_body(vec![CStmt::Return(Some(simplified))]);

        let reachable = crate::ast::strip_render_observations(
            &mut function,
            owner.expected_count())
        .expect("linear identity observations remain well formed");

        assert!(reachable.contains(result_id));
        assert!(!reachable.contains(first_id));
        assert!(!reachable.contains(second_id));
        assert_eq!(
            function.body,
            vec![CStmt::Return(Some(CExpr::binary(
                BinaryOp::Mul,
                ctx.name_ref("x"),
                CExpr::IntLit(3),
            )))]
        );
    }

    #[test]
    fn assignment_cleanup_is_observation_transparent() {
        let ctx = FoldingContext::new(64);
        let lhs = ctx.name_ref("x");
        let plain = ctx.assign_stmt(lhs.clone(), ctx.name_ref("x"));
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (_, observed_rhs) = owner
            .observe_expr(ctx.name_ref("x"))
            .expect("assignment observation");
        let marked = ctx.assign_stmt(lhs, observed_rhs);

        assert_eq!(plain, None);
        assert_eq!(
            marked, plain,
            "metadata around a semantic self-assignment must not keep the statement alive"
        );
    }

    #[test]
    fn assignment_definition_safeguard_is_observation_transparent() {
        let mut ctx = FoldingContext::new(64);
        ctx.state
            .analysis_ctx
            .use_info
            .insert_definition_for_name_if_absent("t1", ctx.name_ref("prev"));

        let plain = ctx
            .assign_stmt(ctx.name_ref("prev"), ctx.name_ref("t1"))
            .expect("the source assignment must survive definition rewriting");
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (write_id, observed_lhs) = owner
            .observe_expr(ctx.name_ref("prev"))
            .expect("assignment target observation");
        let (use_id, observed_rhs) = owner
            .observe_expr(ctx.name_ref("t1"))
            .expect("assignment source observation");
        let marked = ctx
            .assign_stmt(observed_lhs, observed_rhs)
            .expect("metadata must not turn the source assignment into a self-assignment");
        let mut function = CFunction::new("assign", CType::Void).with_body(vec![marked]);
        let reachable = crate::ast::strip_render_observations(
            &mut function,
            owner.expected_count())
        .expect("the source observation must survive exactly once");

        assert!(reachable.contains(write_id));
        assert!(reachable.contains(use_id));
        assert_eq!(function.body, vec![plain]);
    }

    #[test]
    fn assignment_pointer_guard_is_observation_transparent() {
        let ctx = FoldingContext::new(64);
        let rhs = CExpr::Deref(Box::new(ctx.name_ref("arg1")));
        let plain = ctx
            .assign_stmt(ctx.name_ref("arg1"), rhs.clone())
            .expect("a pointer-shaped RHS must survive the generic-argument safeguard");
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (use_id, observed_rhs) = owner
            .observe_expr(rhs)
            .expect("pointer RHS observation");
        let marked = ctx
            .assign_stmt(ctx.name_ref("arg1"), observed_rhs)
            .expect("metadata must not hide a pointer-shaped RHS");
        let mut function = CFunction::new("assign", CType::Void).with_body(vec![marked]);
        let reachable = crate::ast::strip_render_observations(
            &mut function,
            owner.expected_count())
        .expect("the pointer observation must survive exactly once");

        assert!(reachable.contains(use_id));
        assert_eq!(function.body, vec![plain]);
    }

    #[test]
    fn scalar_address_artifact_classification_is_observation_transparent() {
        let ctx = FoldingContext::new(64);
        let plain = CExpr::AddrOf(Box::new(ctx.name_ref("local_8")));
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (_, observed) = owner
            .observe_expr(plain.clone())
            .expect("address observation");

        assert!(ctx.expr_is_address_artifact_in_scalar_context(&plain));
        assert_eq!(
            ctx.expr_is_address_artifact_in_scalar_context(&observed),
            ctx.expr_is_address_artifact_in_scalar_context(&plain),
            "observation metadata must not change scalar address classification"
        );
    }

    #[test]
    fn assignment_cast_policy_is_observation_transparent() {
        let ctx = FoldingContext::new(64);
        let target = CType::Int(32);
        let source = CType::UInt(64);
        let cast = CExpr::cast(target.clone(), ctx.name_ref("value"));
        let plain = ctx.cast_expr_if_needed(cast.clone(), target.clone(), Some(&source));
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (use_id, observed) = owner
            .observe_expr(cast)
            .expect("cast observation");
        let marked = ctx.cast_expr_if_needed(observed, target, Some(&source));
        let mut function = CFunction::new("cast", CType::Void)
            .with_body(vec![CStmt::Expr(marked)]);
        let reachable = crate::ast::strip_render_observations(
            &mut function,
            owner.expected_count())
        .expect("the cast observation must survive exactly once");

        assert!(reachable.contains(use_id));
        assert_eq!(function.body, vec![CStmt::Expr(plain)]);
    }

    #[test]
    fn typed_literal_rewrite_is_observation_transparent() {
        let ctx = FoldingContext::new(64);
        let target = CType::Int(8);
        let literal = CExpr::UIntLit(255);
        let plain = ctx.rewrite_typed_assignment_literal_expr(literal.clone(), &target);
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (use_id, observed) = owner
            .observe_expr(literal)
            .expect("literal observation");
        let marked = ctx.rewrite_typed_assignment_literal_expr(observed, &target);
        let mut function = CFunction::new("literal", CType::Void)
            .with_body(vec![CStmt::Expr(marked)]);
        let reachable = crate::ast::strip_render_observations(
            &mut function,
            owner.expected_count())
        .expect("the literal observation must survive exactly once");

        assert!(reachable.contains(use_id));
        assert_eq!(plain, CExpr::IntLit(-1));
        assert_eq!(function.body, vec![CStmt::Expr(plain)]);
    }

    #[test]
    fn test_identity_add_repeated_scaled_term() {
        let ctx = FoldingContext::new(64);
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
                ctx.name_ref("arg1"))),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("t2_2"),
                ctx.name_ref("arg2"))),
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
                vec![ctx.name_ref("ctx")]),
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
        let mut observations = crate::ast::RenderObservationOwner::new();
        let (call_id, observed_call) = observations
            .observe_expr(call.clone())
            .expect("call observation");
        let (write_id, observed_assignment) = observations
            .observe_stmt(CStmt::Expr(CExpr::assign(
                ctx.name_ref("x0_8"),
                observed_call,
            )))
            .expect("assignment observation");
        let stmts = vec![
            observed_assignment,
            CStmt::Return(Some(ctx.name_ref("x0_3"))),
        ];

        let pruned = ctx.prune_dead_temp_assignments(stmts);
        let mut function = CFunction::new("dead_call_result", CType::Void).with_body(pruned);
        let reachable = crate::ast::strip_render_observations(
            &mut function,
            observations.expected_count())
        .expect("demoted call preserves a valid marker domain");

        assert_eq!(
            function.body,
            vec![
                CStmt::Expr(call),
                CStmt::Return(Some(ctx.name_ref("x0_3"))),
            ]
        );
        assert!(reachable.contains(call_id));
        assert!(
            !reachable.contains(write_id),
            "the eliminated assignment must not earn rendered write coverage"
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
                ctx.name_ref("v"))),
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
                    CExpr::IntLit(64)),
            )),
            CStmt::If {
                cond: CExpr::binary(
                    BinaryOp::Gt,
                    ctx.name_ref("len"),
                    CExpr::IntLit(100)),
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
                    CExpr::IntLit(1)),
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
                rhs.clone())),
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
                ctx.name_ref("arg2"))),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("local_10"),
                ctx.name_ref("arg3"),
            )),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("stack_8"),
                ctx.name_ref("arg1"))),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("stack"),
                ctx.name_ref("arg2"))),
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
                ctx.name_ref("arg1"))),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("eax_3"),
                CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("eax_2"),
                    ctx.name_ref("eax_2")),
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
            reads.contains(&test_symbol(&ctx, "arg1"))
                && !reads.contains(&test_symbol(&ctx, "eax_2")),
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
                    CExpr::IntLit(1)),
            )),
        ];

        let propagated = ctx.propagate_ephemeral_copies(stmts);
        let Some((_, rhs)) = FoldingContext::assignment_target_and_rhs(&propagated[1]) else {
            panic!("expected assignment at propagated[1]");
        };
        let mut reads = HashSet::new();
        ctx.collect_expr_reads(rhs, &mut reads);
        assert!(
            reads.contains(&test_symbol(&ctx, "eax_2")),
            "Call RHS should not be used for copy-forward substitution"
        );
    }

    #[test]
    fn test_propagate_ephemeral_copies_invalidates_alias_when_source_redefined() {
        let ctx = FoldingContext::new(64);
        let stmts = vec![
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("eax_2"),
                ctx.name_ref("rdi_1"))),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("rdi_1"),
                CExpr::IntLit(42))),
            CStmt::Expr(CExpr::assign(
                ctx.name_ref("eax_3"),
                CExpr::binary(
                    BinaryOp::Add,
                    ctx.name_ref("eax_2"),
                    CExpr::IntLit(1)),
            )),
        ];

        let propagated = ctx.propagate_ephemeral_copies(stmts);
        let Some((_, rhs)) = FoldingContext::assignment_target_and_rhs(&propagated[2]) else {
            panic!("expected assignment at propagated[2]");
        };
        let mut reads = HashSet::new();
        ctx.collect_expr_reads(rhs, &mut reads);
        assert!(
            reads.contains(&test_symbol(&ctx, "eax_2")),
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
                    CExpr::IntLit(1)),
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
        }).expect("supported copy lowering");
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
        }).expect("supported copy lowering");
        assert!(
            stmt.is_none(),
            "version-0 return-register phi carriers should not render as source assignments"
        );

        let real_copy = ctx.op_to_stmt(&SSAOp::Copy {
            dst: make_var("EAX", 1, 4),
            src: make_var("EDI", 0, 4),
        }).expect("supported copy lowering");
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
            ctx.name_ref("edi"));
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
                    ctx.name_ref("b")),
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
                    ctx.name_ref("b")),
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
                ctx.name_ref("zf_1")),
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
            CExpr::call(CExpr::External { name: "sym.helper".to_string(), kind: crate::symbol::ExternalKind::Function,
                }, vec![],
            ),
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
                CExpr::IntLit(-8)),
        );

        assert!(
            ctx.is_materialized_call_result_stack_home_store(&addr, &val),
            "exact FunctionFacts call-result owner should suppress the redundant stack-home store"
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
        let stmts = ctx
            .fold_block(exit_block, exit_block.addr)
            .expect("supported block lowering");
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
        ctx.state.analysis_ctx.use_info.insert_semantic_value_for_name(&eax.display_name(), crate::analysis::SemanticValue::Load {
                space: r2il::SpaceId::Ram,
                addr: crate::analysis::NormalizedAddr {
                    base: crate::analysis::BaseRef::Value(crate::analysis::ValueRef::from(arr_src,
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
        let expr = ctx
            .get_return_expr(&eax)
            .expect("fixture return expression should lower");
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
        install_test_param_aliases(&mut ctx,
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
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

        let expr = ctx
            .get_return_expr(&ret)
            .expect("fixture return expression should lower");
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
        install_test_param_aliases(&mut ctx,
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
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

        let expr = ctx
            .get_return_expr(&ret)
            .expect("fixture return expression should lower");
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
    fn test_observed_x86_negative_index_visible_deref_promotes_to_subscript() {
        let mut ctx = FoldingContext::new(64);
        install_test_param_aliases(&mut ctx,
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
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
                    ctx.name_ref("arg2")),
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
        install_test_param_aliases(&mut ctx,
            [
                ("rdi".to_string(), "arg1".to_string()),
                ("esi".to_string(), "arg2".to_string()),
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
    fn visible_expression_quality_is_observation_transparent_in_every_context() {
        let ctx = make_x86_64_ctx();
        let plain = CExpr::binary(
            BinaryOp::Ne,
            ctx.name_ref("arg1"),
            CExpr::IntLit(0));
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (_, inner) = owner
            .observe_expr(plain.clone())
            .expect("inner quality observation");
        let (_, marked) = owner
            .observe_expr(inner)
            .expect("outer quality observation");

        for context in [
            VisibleExprContext::Generic,
            VisibleExprContext::ScalarPredicate,
            VisibleExprContext::ScalarReturn,
        ] {
            assert_eq!(
                ctx.debug_visible_expr_quality(&marked, context),
                ctx.debug_visible_expr_quality(&plain, context),
                "observation wrappers must have zero ranking weight in {context:?}"
            );
        }
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
            Some(ctx.name_ref("var_4h"))
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
            Ok(CExpr::External {
                name: "sym.imp.fact_helper".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            })
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
            .expect("supported call lowering")
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
            .expect("supported call lowering")
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
            ctx.certified_call_args_for_site(0x1000, 2)
                .expect("exact callsite arguments")
                .args,
            vec![CExpr::IntLit(7)],
            "certificate rendering must ignore stale PreparedSemanticView argument values"
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
            .expect("supported call lowering")
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
            .expect("supported call lowering")
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
        let (normalized, origins) = crate::normalize::materialize_certified_loop_carriers(
            prepared.function(),
            &prepared,
            &render_facts,
        )
        .expect("genuine noncarrier normalization must validate");
        assert!(
            normalized
                .get_block(0x181c)
                .is_some_and(|block| !block.phis.is_empty()),
            "ordinary merge phis must remain immutable certified expressions"
        );
        let fold_blocks = normalized.blocks().cloned().collect::<Vec<_>>();
        let base_ctx = make_x86_64_ctx_with_prepared(&prepared);
        let mut inputs = base_ctx.inputs;
        inputs.normalization_origins = Some(Box::leak(Box::new(origins)));
        let mut ctx = FoldingContext::from_inputs(inputs);
        ctx.analyze_blocks(&fold_blocks);

        let left_stmts = ctx.fold_block(
            normalized.get_block(0x1814).expect("left predecessor"),
            0x1814,
        ).expect("supported left-block lowering");
        let right_stmts = ctx.fold_block(
            normalized.get_block(0x1818).expect("right predecessor"),
            0x1818,
        ).expect("supported right-block lowering");
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
    fn synthetic_normalization_sites_cannot_discharge_shifted_source_effects() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1900, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(0, 8),
        });
        entry.push(R2ILOp::Branch {
            target: Varnode::constant(0x1904, 8),
        });

        let mut header = R2ILBlock::new(0x1904, 4);
        header.push(R2ILOp::CBranch {
            cond: Varnode::register(0x10, 8),
            target: Varnode::constant(0x190c, 8),
        });

        let mut latch = R2ILBlock::new(0x1908, 4);
        latch.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(1, 8),
        });
        latch.push(R2ILOp::Branch {
            target: Varnode::constant(0x1904, 8),
        });

        let mut exit = R2ILBlock::new(0x190c, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let prepared = prepared_from_r2il_blocks(&[entry, header, latch, exit], &arch)
            .with_name("normalization_origin_effect_gate");
        let render_facts = test_render_facts(&prepared);
        let (normalized, origins) = crate::normalize::materialize_certified_loop_carriers(
            prepared.function(),
            &prepared,
            &render_facts,
        )
        .expect("genuine loop normalization must validate");
        origins
            .validate(&normalized, &prepared, Some(&render_facts))
            .expect("genuine normalized loop origins must remain sealed");

        let graph = prepared.graph();
        let (block_addr, synthetic_idx, shifted_idx, shifted_inst) = graph
            .block_order
            .iter()
            .find_map(|block_id| {
                let block_addr = graph.block(*block_id)?.addr;
                let block = normalized.get_block(block_addr)?;
                let synthetic_idx = (0..block.ops.len()).find(|op_idx| {
                    matches!(
                        origins.origin(crate::normalize::NormalizedOpSite {
                            block: *block_id,
                            op_idx: *op_idx,
                        }),
                        Some(crate::normalize::NormalizedOpOrigin::PhiEdgeCopy(_))
                            | Some(crate::normalize::NormalizedOpOrigin::RelocatedInitializer(
                                _
                            ))
                    )
                })?;
                let (shifted_idx, shifted_inst) =
                    (synthetic_idx + 1..block.ops.len()).find_map(|op_idx| {
                        match origins.origin(crate::normalize::NormalizedOpSite {
                            block: *block_id,
                            op_idx,
                        }) {
                            Some(crate::normalize::NormalizedOpOrigin::Original(inst))
                                if graph.op_site_for_inst(*inst)?.1 != op_idx =>
                            {
                                Some((op_idx, *inst))
                            }
                            _ => None,
                        }
                    })?;
                Some((block_addr, synthetic_idx, shifted_idx, shifted_inst))
            })
            .expect("materialized loop must insert a synthetic op before an original terminator");

        let base_ctx = make_x86_64_ctx_with_prepared(&prepared);
        let mut inputs = base_ctx.inputs;
        inputs.normalization_origins = Some(Box::leak(Box::new(origins)));
        let ctx = FoldingContext::from_inputs(inputs);
        assert_eq!(
            ctx.source_op_site_for_normalized_op(block_addr, synthetic_idx),
            None,
            "synthetic geometry must never fall back to its normalized numeric site"
        );
        assert_eq!(
            ctx.source_op_site_for_normalized_op(block_addr, shifted_idx),
            graph.op_site_for_inst(shifted_inst),
            "the shifted original must resolve through its exact InstId"
        );
        let synthetic_obligations = ctx.exact_effect_obligations_for_normalized_value(
            EffectOccurrenceKind::Expression,
            block_addr,
            synthetic_idx,
            None,
        );
        assert!(
            synthetic_obligations.iter().all(|id| {
                id.kind == r2ssa::SemanticObligationKind::LiveStateTransition
                    && matches!(id.instruction.site, r2ssa::CanonicalInstructionSite::Phi(_))
            }),
            "a synthetic phi operation may carry only an obligation that exists for its exact original input edge"
        );
        let obligations = ctx.exact_effect_obligations_for_normalized_value(
            EffectOccurrenceKind::Expression,
            block_addr,
            shifted_idx,
            None,
        );
        let shifted_instruction = prepared
            .obligations()
            .instruction_for_inst(shifted_inst)
            .expect("shifted source terminator has canonical identity")
            .id;
        assert!(
            !obligations.is_empty()
                && obligations
                    .iter()
                    .all(|id| id.instruction == shifted_instruction),
            "the shifted normalized index must discharge only exact obligations of its original InstId"
        );
    }

    #[test]
    fn rendered_memory_component_does_not_claim_other_obligations_on_its_instruction() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1920, 4);
        entry.push(R2ILOp::Load {
            dst: Varnode::register(0, 8),
            space: r2il::SpaceId::Ram,
            addr: Varnode::register(0x10, 8),
        });
        entry.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("exact_memory_obligation_proof");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_certified_function_facts(&mut ctx);
        let fact = ctx
            .inputs
            .render_facts()
            .and_then(|facts| facts.memory_access_for_op(0x1920, 0, false, r2il::SpaceId::Ram))
            .expect("genuine load has one canonical memory fact")
            .clone();
        assert!(
            prepared
                .obligations()
                .obligations_for_inst(fact.access.inst)
                .any(|obligation| {
                    obligation.id.kind == r2ssa::SemanticObligationKind::LiveValueProducer
                }),
            "fixture must put multiple obligations on the load instruction"
        );

        let obligations = ctx.exact_effect_obligations_for_source_memory(
            EffectOccurrenceKind::MemoryRead,
            fact.block_addr,
            fact.op_index,
            fact.space,
            Some(fact.address),
            fact.value,
        );

        assert_eq!(obligations.len(), 1);
        assert!(obligations.iter().all(|id| {
            id.kind == r2ssa::SemanticObligationKind::ObservableMemoryRead
                && id.component
                    == r2ssa::SemanticObligationComponent::MemoryAccess(fact.access.ordinal)
        }));
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
        let adapter = CertifiedRenderPlan::new(
            &function_facts,
            &view,
            CertifiedRenderContext::new(&prepared, &render),
        );
        assert_eq!(
            adapter.call_arg_expr((0x1000, 2), arg_value, |_| false),
            Some(crate::symbol::var_ref(&symbols, "n"))
        );

        let unrenderable = render_facts(false);
        let adapter = CertifiedRenderPlan::new(
            &function_facts,
            &view,
            CertifiedRenderContext::new(&prepared, &unrenderable),
        );
        assert_eq!(
            adapter.call_arg_expr((0x1000, 2), arg_value, |_| false),
            None
        );

        let wrong_value_view = prepared_view(r2ssa::ValueId(9999), crate::symbol::var_ref(&symbols, "n"));
        let adapter = CertifiedRenderPlan::new(
            &function_facts,
            &wrong_value_view,
            CertifiedRenderContext::new(&prepared, &render),
        );
        assert_eq!(
            adapter.call_arg_expr((0x1000, 2), arg_value, |_| false),
            None
        );

        let raw_storage_view = prepared_view(arg_value, crate::symbol::var_ref(&symbols, "tmp:raw_1"));
        let adapter = CertifiedRenderPlan::new(
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
                CExpr::IntLit(1)),
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
    fn prepared_generic_zero_compare_yields_to_local_compare_recovery() {
        let mut ctx = make_x86_64_ctx();
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(PreparedSemanticView {
            branch_predicate_expr_by_block: BTreeMap::from([(
                0x1000,
                CExpr::binary(
                    BinaryOp::Ne,
                    ctx.name_ref("var_8h"),
                    CExpr::IntLit(0)),
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
            .expect("supported load lowering")
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
        install_test_param_aliases(ctx, HashMap::from([
            ("RDI".to_string(), "arg0".to_string()),
            ("rdi".to_string(), "arg0".to_string()),
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
            ctx.local_post_call_source_for_var_in_block(&block, &copied, 0),
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
            ctx.local_post_call_source_for_var_in_block(&block, &out, 0),
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
            ctx.local_post_call_source_for_var_in_block(&direct, &rax, 16),
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
            ctx.local_post_call_source_for_var_in_block(&chained, &prev, 0)
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
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&slot.display_name(), CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(-8)),
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
            ctx.local_post_call_source_for_var_in_block(&block, &copied, 0),
            Some(source_call),
            "stack reloads must preserve the canonical producing call source"
        );
    }

    #[test]
    fn local_post_call_source_refuses_custom_space_stack_shaped_reload() {
        let mut ctx = make_x86_64_ctx();
        let rax = make_var("rax", 1, 8);
        let slot = make_var("tmp:slot", 1, 8);
        let loaded = make_var("tmp:loaded", 1, 8);
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&slot.display_name(), CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(-8)),
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
            ctx.local_post_call_source_for_var_in_block(&block, &loaded, 0,)
                .is_none(),
            "stack-shaped accesses in a custom address space cannot inherit a RAM call-result home"
        );
    }

    #[test]
    fn local_post_call_source_refuses_mismatched_stack_reload_offset() {
        let mut ctx = make_x86_64_ctx();
        let rax = make_var("rax", 1, 8);
        let stored_slot = make_var("tmp:stored_slot", 1, 8);
        let loaded_slot = make_var("tmp:loaded_slot", 1, 8);
        let loaded = make_var("tmp:loaded", 1, 8);
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&stored_slot.display_name(), CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(-8)),
        );
        ctx.state.analysis_ctx.use_info.insert_definition_for_name_if_absent(&loaded_slot.display_name(), CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("rbp"),
                CExpr::IntLit(-16)),
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
            ctx.local_post_call_source_for_var_in_block(&block, &loaded, 0)
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
                CExpr::IntLit(-8)),
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
            ctx.local_post_call_source_for_var_in_block(&block, &loaded, 0)
                .is_none(),
            "stack reload source tracing must enforce the recursion budget"
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
            let arch = make_test_arch_x86_64();
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
                    ctx.state.analysis_ctx.use_info.insert_call_result_source_alias(&store_val.to_ascii_lowercase(), source_call,
                        );
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
                        .insert_call_result_source_alias(&store_val.to_string(), (source_call.0, source_call.1 + 1),
                        );
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
