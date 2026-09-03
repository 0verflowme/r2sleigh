#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        collections::{BTreeMap, BTreeSet, HashMap},
        ops::Deref,
        rc::Rc,
        sync::Arc,
    };

    use crate::fold::context::{EffectOccurrenceKind, empty_function_facts};
    use crate::{
        FoldArchConfig, FoldInputs,
        ast::{CFunction, CLocal},
    };
    use r2il::{
        ArchSpec, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef, RegisterProjection,
        RegisterProjectionDisposition, RegisterStorage, SpaceId, Varnode,
    };
    use r2ssa::SSAFunction;
    use r2types::{CalleeFact, CalleeReturnRelation};

    #[derive(Debug, Clone)]
    struct FunctionType {
        return_type: CType,
        params: Vec<CType>,
        variadic: bool,
    }

    impl From<FunctionType> for r2types::FunctionType {
        fn from(value: FunctionType) -> Self {
            Self {
                return_type: value.return_type.clone(),
                params: value.params.to_vec(),
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
        arch.register_projections = arch
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
            .collect();
        arch.register_projections
            .sort_by_key(|projection| projection.written);
        // The architecture says where it returns a value, so a call result is
        // distinguishable without a list of register spellings.
        arch.return_registers = vec![RegisterDef::new("RAX", 0x00, 8)];
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
        prepared_from_r2il_blocks_with_call_arguments(blocks, arch, 0)
    }

    fn prepared_from_r2il_blocks_with_call_arguments(
        blocks: &[R2ILBlock],
        arch: &ArchSpec,
        call_argument_count: usize,
    ) -> SourceOwnedPreparedFixture {
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let revision = b"r2dec-fold-pipeline-source-v1";
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
            .iter()
            .copied()
            .enumerate()
            .map(|(index, offset)| {
                r2ssa::SourceAbiParameterSpec::new(index as u32, storage(offset))
            })
            .collect::<Vec<_>>();
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            revision.to_vec(),
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
        assert!(call_argument_count <= parameter_offsets.len());
        let call_site_interfaces = blocks
            .iter()
            .flat_map(|block| {
                block.ops.iter().enumerate().filter_map(|(op_index, op)| {
                    let target = match op {
                        R2ILOp::Call { target } | R2ILOp::CallInd { target } => target,
                        _ => return None,
                    };
                    Some(
                        r2ssa::SourceCallSiteInterface::new(
                            revision.to_vec(),
                            r2ssa::SourceCallSiteIdentity::new(
                                block.addr,
                                op_index,
                                r2ssa::CanonicalStorageId::from_varnode(target),
                            ),
                            true,
                            calling_convention,
                            parameter_offsets
                                .iter()
                                .copied()
                                .take(call_argument_count)
                                .enumerate()
                                .map(|(index, offset)| {
                                    r2ssa::SourceCallArgumentSpec::new(
                                        index as u32,
                                        storage(offset),
                                    )
                                }),
                            false,
                            false,
                            r2ssa::SourceCallResult::Void,
                        )
                        .expect("exact test callsite interface"),
                    )
                })
            })
            .collect();
        source_owned_fixture(
            r2ssa::SsaArtifact::for_decompile_with_interfaces(
                blocks,
                Some(arch),
                Some(interface),
                call_site_interfaces,
            )
            .expect("prepared SSA should build"),
        )
    }

    fn prepared_x86_with_demo_struct_parameter(
        blocks: &[R2ILBlock],
        arch: &ArchSpec,
    ) -> SourceOwnedPreparedFixture {
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let parameters = [0x10, 0x18, 0x38, 0x40, 0x48, 0x50]
            .into_iter()
            .enumerate()
            .map(|(index, offset)| {
                r2ssa::SourceAbiParameterSpec::new(index as u32, storage(offset))
            })
            .collect::<Vec<_>>();
        let scalar_carrier =
            r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::Full, 0, 64);
        let type_graph = r2ssa::SourceTypeGraph::new(
            [
                r2ssa::SourceType::new(
                    0,
                    r2ssa::SourceTypeKind::Struct { aggregate_id: 0 },
                    128,
                    64,
                ),
                r2ssa::SourceType::new(1, r2ssa::SourceTypeKind::UnsignedInteger, 64, 64),
                r2ssa::SourceType::new(
                    2,
                    r2ssa::SourceTypeKind::Pointer { target_type_id: 0 },
                    64,
                    64,
                ),
            ],
            [r2ssa::SourceAggregateLayout::new(
                0,
                0,
                128,
                64,
                "DemoStruct",
                [
                    r2ssa::SourceAggregateMember::new(0, 1, 0, 64, "prefix"),
                    r2ssa::SourceAggregateMember::new(1, 1, 64, 64, "hash"),
                ],
            )],
        )
        .expect("valid exact DemoStruct source type graph");
        let parameter_types = std::iter::once(r2ssa::SourceLogicalValue::new(2, scalar_carrier))
            .chain((1..parameters.len()).map(|_| r2ssa::SourceLogicalValue::new(1, scalar_carrier)))
            .collect::<Vec<_>>();
        let interface = r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
            b"r2dec-fold-pipeline-demo-struct-v1".to_vec(),
            "sysv64",
            parameters,
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
            parameter_types,
            Some(r2ssa::SourceLogicalValue::new(1, scalar_carrier)),
            Some(type_graph),
        )
        .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
        .expect("exact typed source interface");
        source_owned_fixture(
            r2ssa::SsaArtifact::for_decompile_with_interface(blocks, Some(arch), interface)
                .expect("prepared typed SSA should build"),
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

    fn prepared_x86_with_parameter_home(
        blocks: &[R2ILBlock],
        arch: &ArchSpec,
        parameter_index: u32,
        offset: i64,
    ) -> SourceOwnedPreparedFixture {
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let parameters = [0x10, 0x18, 0x38, 0x40, 0x48, 0x50]
            .into_iter()
            .enumerate()
            .map(|(index, offset)| {
                r2ssa::SourceAbiParameterSpec::new(index as u32, storage(offset))
            })
            .collect::<Vec<_>>();
        let home_storage = parameters[parameter_index as usize].storage();
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"r2dec-fold-pipeline-param-home-v1".to_vec(),
            "sysv64",
            parameters,
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [r2ssa::SourceStackSlotSpec::new_parameter_home(
                r2ssa::StackAddressBase::FramePointer,
                storage(0x20),
                offset,
                8,
                parameter_index,
                home_storage,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
        .and_then(|interface| interface.with_frame_pointer_storage(storage(0x20)))
        .expect("exact parameter-home source interface");
        source_owned_fixture(
            r2ssa::SsaArtifact::for_decompile_with_interface(blocks, Some(arch), interface)
                .expect("prepared parameter-home SSA should build"),
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

    fn make_x86_64_ctx<'a>() -> FoldingContext<'a> {
        let arch = Box::leak(Box::new(FoldArchConfig {
            ptr_size: 8,
            arg_regs: vec![
                "rdi".to_string(),
                "rsi".to_string(),
                "rdx".to_string(),
                "rcx".to_string(),
                "r8".to_string(),
                "r9".to_string(),
            ],
        }));
        let empty_u64 = Box::leak(Box::new(HashMap::new()));
        let empty_stack_slots = Box::leak(Box::new(BTreeMap::new()));
        let empty_visible = Box::leak(Box::new(Vec::new()));
        FoldingContext::from_inputs(FoldInputs {
            normalization_origins: None,
            observation_journal: None,
            binding_names: None,
            arch,
            function_names: empty_u64,
            binary_symbols: empty_u64,
            function_facts: empty_function_facts(),
            stack_slots: empty_stack_slots,
            visible_bindings: empty_visible,
            function_return_type: None,
            prepared_ssa: None,
            prepared_semantic_view: None,
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
                        let r2ssa::CallArgumentLocation::Register { storage } = argument.location
                        else {
                            return None;
                        };
                        Some(r2types::RegisterCallArgumentLocationFact {
                            index: argument.index,
                            value: argument.value,
                            storage,
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
                        variadic: cert.variadic,
                        fixed_argument_count: cert.fixed_argument_count,
                        register_argument_locations,
                        stack_argument_locations,
                    },
                ))
            })
            .collect();
        r2types::FunctionCallsiteFacts { by_callsite }
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
                Rc::clone(names),
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
            Rc::clone(names),
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

    fn enter_exact_test_site(ctx: &FoldingContext<'_>, block_addr: u64, op_idx: usize) {
        ctx.current_block_addr.set(Some(block_addr));
        ctx.current_op_idx.set(Some(op_idx));
    }

    #[test]
    fn observed_clearing_narrow_register_write_applies_exact_zero_extension() {
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
        // A narrow register write as the lift states it: the arithmetic write,
        // then Sleigh's own extension of the whole carrier. An arithmetic write
        // rather than a copy so the narrow value survives as its own
        // definition instead of being folded into its uses -- and each of the
        // extra readers below is itself read, because a reader nothing
        // observes is elided and no longer counts against folding.
        entry.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 4),
            a: Varnode::register(0, 4),
            b: Varnode::constant(0xaa, 4),
        });
        entry.push(R2ILOp::IntZExt {
            dst: Varnode::register(0, 8),
            src: Varnode::register(0, 4),
        });
        for (offset, address) in [(0x20, 0x2010), (0x28, 0x2018)] {
            entry.push(R2ILOp::IntAdd {
                dst: Varnode::unique(offset, 4),
                a: Varnode::register(0, 4),
                b: Varnode::constant(1, 4),
            });
            entry.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::constant(address, 8),
                val: Varnode::unique(offset, 4),
            });
        }
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2000, 8),
            val: Varnode::register(0, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("observed_exact_narrow_register_write");
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let copy_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::IntAdd { dst, .. } if dst.size == 4))
            .expect("low-register write");
        let copy_inst = prepared
            .graph()
            .inst_id_for_op_site(block.addr, copy_idx)
            .expect("copy graph instruction");

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (plan, _, _) = install_observed_lowering(&mut ctx, &prepared);
        enter_exact_test_site(&ctx, block.addr, copy_idx);
        assert!(matches!(
            plan.write_disposition(copy_inst),
            Some(r2ssa::MachineWriteDisposition::Exact(
                r2ssa::MachineWriteProjection::ZeroExtend {
                    from_width_bits: 32,
                    to_width_bits: 64,
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
        // One cast, not two. The write zero-extends a thirty-two bit value
        // into the sixty-four bit carrier, and the addition already produces
        // that thirty-two bit value: C computes `uint32_t + uint32_t` in
        // `uint32_t`. The `(uint32_t)` this once spelled underneath said so a
        // second time. What has to be spelled is the extension itself, and
        // that it is an extension of an unsigned value rather than a signed
        // one, which the operand's own type carries.
        let CExpr::Cast {
            ty:
                CType::Int {
                    bits: 64,
                    signedness: r2types::Signedness::Unsigned,
                },
            expr: extended,
            ..
        } = copy_rhs.unobserved()
        else {
            panic!("the write must zero-extend into the carrier: {copy_rhs:?}");
        };
        assert!(
            matches!(
                extended.unobserved(),
                CExpr::Binary {
                    op: BinaryOp::Add,
                    ..
                }
            ),
            "the extension applies to the thirty-two bit addition itself, \
             with no conversion restating the width it already has: {extended:?}"
        );

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
        // The address is computed once and read twice, so it keeps a binding
        // of its own. A single reader would fold the subtraction into the
        // load, and this test is about what the binding spells.
        entry.push(R2ILOp::Load {
            dst: Varnode::unique(0x208, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        for offset in [0x210, 0x218] {
            entry.push(R2ILOp::IntAdd {
                dst: Varnode::unique(offset, 4),
                a: Varnode::unique(0x200, 4),
                b: Varnode::constant(1, 4),
            });
        }
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
        enter_exact_test_site(&ctx, block.addr, load_idx);
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
        assert!(matches!(
            plan.write_disposition(load_inst),
            Some(r2ssa::MachineWriteDisposition::Exact(_))
        ));
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
        // This fixture intentionally withholds an upstream frame-pointer role,
        // so the opaque address value remains an ordinary binding.  The exact
        // per-use stack-object projection must still render the access without
        // reinterpreting that binding's spelling downstream.
        assert!(matches!(
            names.require_value(address.binding().value()),
            Ok(crate::binding_plan::PlannedValueSymbol::Bound(_))
        ));
        assert_eq!(*ctx.observation_error.borrow(), None);
    }

    #[test]
    fn signed_borrow_uses_one_exact_projection_per_operand() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntSBorrow {
            dst: Varnode::unique(0x100, 1),
            a: Varnode::constant(i64::MAX as u64, 8),
            b: Varnode::constant(u64::MAX, 8),
        });
        entry.push(R2ILOp::IntZExt {
            dst: Varnode::unique(0x108, 8),
            src: Varnode::unique(0x100, 1),
        });
        for offset in [0x110, 0x118] {
            entry.push(R2ILOp::IntAdd {
                dst: Varnode::unique(offset, 8),
                a: Varnode::unique(0x108, 8),
                b: Varnode::constant(1, 8),
            });
        }
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2000, 8),
            val: Varnode::unique(0x110, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("signed_borrow_projection");
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (_plan, _names, _journal) = install_observed_lowering(&mut ctx, &prepared);

        enter_exact_test_site(&ctx, block.addr, 0);
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[0], block.addr, 0)
            .expect("signed borrow has exact scalar lowering")
            .expect("signed borrow definition");
        let rendered = format!("{stmt:?}");
        assert!(
            rendered.contains("r2sleigh_int_sborrow_64"),
            "signed borrow must use the external width-safe helper: {rendered}"
        );
        assert_eq!(*ctx.observation_error.borrow(), None);
    }

    #[test]
    fn population_count_consumes_the_upstream_machine_projection() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::PopCount {
            dst: Varnode::unique(0x100, 1),
            src: Varnode::constant(0xf0f0, 8),
        });
        entry.push(R2ILOp::IntZExt {
            dst: Varnode::unique(0x108, 8),
            src: Varnode::unique(0x100, 1),
        });
        for offset in [0x110, 0x118] {
            entry.push(R2ILOp::IntAdd {
                dst: Varnode::unique(offset, 8),
                a: Varnode::unique(0x108, 8),
                b: Varnode::constant(1, 8),
            });
        }
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2000, 8),
            val: Varnode::unique(0x110, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("population_count_projection");
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (plan, _names, _journal) = install_observed_lowering(&mut ctx, &prepared);
        let inst = prepared
            .graph()
            .inst_id_for_op_site(block.addr, 0)
            .expect("population-count instruction");
        assert!(matches!(
            plan.use_disposition(r2ssa::UseSite { inst, input_idx: 0 }),
            Some(r2ssa::MachineUseDisposition::Exact(_))
        ));

        enter_exact_test_site(&ctx, block.addr, 0);
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[0], block.addr, 0)
            .expect("population count has exact scalar lowering")
            .expect("population-count definition");
        assert!(format!("{stmt:?}").contains("__builtin_popcountll"));
        assert_eq!(*ctx.observation_error.borrow(), None);
    }

    #[test]
    fn exact_parameter_home_reuses_one_parameter_binding_identity() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntSub {
            dst: Varnode::unique(0x280, 8),
            a: Varnode::register(0x20, 8),
            b: Varnode::constant(8, 8),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x280, 8),
            val: Varnode::register(0x10, 8),
        });
        let prepared = prepared_x86_with_parameter_home(&[entry], &arch, 0, -8)
            .with_name("exact_parameter_home_binding");
        let render = prepared
            .function_facts()
            .render()
            .expect("source-owned render facts");
        let (object, source_slot) = render
            .certified_entities
            .values()
            .find_map(|entity| match entity {
                r2types::CertifiedEntity::StackSlot {
                    object,
                    source_slot: Some(source_slot),
                    ..
                } => Some((*object, *source_slot)),
                _ => None,
            })
            .expect("exact parameter-home stack certificate");
        assert!(matches!(
            source_slot.role(),
            r2ssa::SourceStackSlotRole::ParameterHome {
                parameter_index: 0,
                ..
            }
        ));

        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (plan, names, _) = install_observed_lowering(&mut ctx, &prepared);
        let parameter_binding = match plan.parameter_disposition(0) {
            Some(crate::binding_plan::ParameterDisposition::Bound { binding, .. }) => binding,
            other => panic!("exact parameter must be bound: {other:?}"),
        };
        assert_eq!(
            plan.stack_object_disposition(object),
            Some(crate::binding_plan::StackObjectDisposition::Bound {
                binding: parameter_binding,
            })
        );
        assert_eq!(
            plan.binding_role(parameter_binding),
            Some(crate::binding_plan::BindingRole::Parameter { slot: 0 })
        );
        let crate::binding_plan::PlannedParameterSymbol::Bound {
            symbol: parameter_symbol,
            ..
        } = names
            .require_parameter_slot(0)
            .expect("parameter binding name");
        let crate::binding_plan::PlannedStackSymbol::Bound(stack_symbol) = names
            .require_stack(object)
            .expect("stack-home binding name");
        assert_eq!(stack_symbol, parameter_symbol);
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
        let (plan, names, journal) = install_observed_lowering(&mut ctx, &prepared);
        let mut body = Vec::new();
        for prefix_idx in 0..store_idx {
            if block.ops[prefix_idx]
                .dst()
                .is_some_and(|dst| ctx.is_dead(dst))
            {
                continue;
            }
            enter_exact_test_site(&ctx, block.addr, prefix_idx);
            if let Some(prefix) = ctx
                .op_to_stmt_with_args(&block.ops[prefix_idx], block.addr, prefix_idx)
                .expect("supported stack-address prefix lowering")
            {
                body.push(prefix);
            }
        }
        enter_exact_test_site(&ctx, block.addr, store_idx);
        let address = match plan.use_disposition(address_site) {
            Some(r2ssa::MachineUseDisposition::MemoryAddress(address)) => *address,
            other => panic!("expected contextual store address, got {other:?}"),
        };
        assert!(matches!(
            names.require_value(address.binding().value()),
            Ok(crate::binding_plan::PlannedValueSymbol::Elided(
                r2ssa::ledger::ElisionReason::DeadStackBase
            ))
        ));
        let memory = ctx
            .certified_memory_access_for_current_op(true)
            .filter(|memory| memory.access == address.memory_access().unwrap())
            .expect("exact source-owned stack write fact")
            .clone();
        let effect_obligations = ctx.exact_effect_obligations_for_source_memory(
            EffectOccurrenceKind::MemoryWrite,
            memory.block_addr,
            memory.op_index,
            memory.space,
            Some(memory.address),
            memory.value,
        );
        assert_eq!(effect_obligations.len(), 1);

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
        assert_eq!(*ctx.observation_error.borrow(), None);
        let value_site = r2ssa::UseSite {
            inst: store_inst,
            input_idx: 1,
        };
        let symbols = Rc::clone(&ctx.symbols);
        drop(ctx);
        body.push(stmt);
        let sealed = seal_observed_lowering(
            &prepared,
            Rc::clone(&plan),
            names,
            journal,
            symbols,
            CType::Void,
            body,
        );
        assert_eq!(
            sealed.observations().use_observation(address_site),
            Some(exact_legacy_use(&plan, address_site))
        );
        assert_eq!(
            sealed.observations().use_observation(value_site),
            Some(exact_legacy_use(&plan, value_site))
        );
        for obligation in effect_obligations {
            assert_eq!(
                sealed.effect_observations().occurrence_count(obligation),
                Some(1)
            );
        }
    }

    fn assert_observed_call_marks_only_graph_target(indirect: bool) {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x10, 8),
            src: Varnode::constant(7, 8),
        });
        let target = if indirect {
            Varnode::register(0x18, 8)
        } else {
            entry.push(R2ILOp::Copy {
                dst: Varnode::unique(0x10, 8),
                src: Varnode::constant(0x401050, 8),
            });
            Varnode::unique(0x10, 8)
        };
        if indirect {
            entry.push(R2ILOp::CallInd { target });
        } else {
            entry.push(R2ILOp::Call { target });
        }
        let prepared = prepared_from_r2il_blocks_with_call_arguments(&[entry], &arch, 1).with_name(
            if indirect {
                "observed_indirect_call_target"
            } else {
                "observed_direct_call_target"
            },
        );
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
        let mut body = Vec::new();
        // The folder skips the copy that materializes a direct call's target,
        // because the call spells the callee's name and the plan elides the
        // value that copy would assign. Lowering it here anyway would ask for
        // an object that by then has no name.
        let target_definitions = prepared
            .graph()
            .def_inst(prepared.graph().inst(inst).expect("call row").inputs[0])
            .into_iter()
            .collect::<std::collections::BTreeSet<_>>();
        for prefix_idx in 0..op_idx {
            if !indirect
                && ctx
                    .source_inst_for_normalized_op(block.addr, prefix_idx)
                    .is_some_and(|prefix_inst| target_definitions.contains(&prefix_inst))
            {
                continue;
            }
            // What `fold_block` does before it lowers anything: a definition
            // the plan inlines has no statement, and asking for one requests
            // the name the plan deliberately withheld. A call's arguments are
            // now foldable -- the callsite certificate is a reader even though
            // the graph records none -- so the staging writes reach this and
            // the loop has to skip them exactly as the folder does.
            if block.ops[prefix_idx]
                .dst()
                .is_some_and(|dst| ctx.should_inline(dst))
            {
                continue;
            }
            enter_exact_test_site(&ctx, block.addr, prefix_idx);
            if let Some(prefix) = ctx
                .op_to_stmt_with_args(&block.ops[prefix_idx], block.addr, prefix_idx)
                .expect("supported call-prefix lowering")
            {
                body.push(prefix);
            }
        }
        enter_exact_test_site(&ctx, block.addr, op_idx);
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[op_idx], block.addr, op_idx)
            .expect("supported call lowering")
            .expect("certified call statement");
        let effect_obligations = ctx.exact_effect_obligations_for_normalized_value(
            EffectOccurrenceKind::Expression,
            block.addr,
            op_idx,
            None,
        );
        assert!(
            !effect_obligations.is_empty(),
            "the exact source call must own call/call-argument obligations"
        );
        let CStmt::Expr(call) = stmt.unobserved() else {
            panic!("expected call expression, got {stmt:?}");
        };
        let CExpr::Call { args, .. } = call.unobserved() else {
            panic!("expected call expression, got {call:?}");
        };
        assert!(
            !args.is_empty(),
            "fixture must render at least one semantic argument: boundary={:?}; certificate={:?}",
            prepared.facts().boundaries.calls.values().next(),
            prepared.callsite_certificate_for_op(block.addr, op_idx),
        );
        assert_eq!(*ctx.observation_error.borrow(), None);
        body.push(stmt);
        for suffix_idx in op_idx + 1..block.ops.len() {
            if block.ops[suffix_idx]
                .dst()
                .is_some_and(|dst| ctx.is_dead(dst))
            {
                continue;
            }
            enter_exact_test_site(&ctx, block.addr, suffix_idx);
            if let Some(suffix) = ctx
                .op_to_stmt_with_args(&block.ops[suffix_idx], block.addr, suffix_idx)
                .expect("supported post-call definition lowering")
            {
                body.push(suffix);
            }
        }
        let symbols = Rc::clone(&ctx.symbols);
        drop(ctx);
        let sealed = seal_observed_lowering(
            &prepared,
            Rc::clone(&plan),
            names,
            journal,
            symbols,
            CType::Void,
            body,
        );

        // A direct call names its callee, which is not a read of the operand's
        // value: the symbol comes from the call site, and the plan elides the
        // value beside it. An indirect call really does read a target the
        // program computed, and there the operand is an ordinary exact use.
        assert_eq!(
            sealed.observations().use_observation(target_site),
            if indirect {
                Some(exact_legacy_use(&plan, target_site))
            } else {
                Some(crate::shadow_report::LegacyUseObservation::Elided(
                    r2ssa::ledger::ElisionReason::DirectCallTarget,
                ))
            }
        );
        assert_eq!(
            sealed
                .observations()
                .use_observation(r2ssa::UseSite { inst, input_idx: 1 }),
            None,
            "rendered semantic arguments are not SSA graph uses of the call"
        );
        for obligation in effect_obligations {
            assert_eq!(
                sealed.effect_observations().occurrence_count(obligation),
                Some(1)
            );
        }
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
        assert_eq!(
            audit.binding_shadow(),
            crate::BindingShadowAuditOutcome::NotRun,
            "an upstream machine refusal must stop before a renderer shadow audit"
        );
        assert_eq!(
            audit.effect_obligations(),
            crate::EffectObligationAudit::NOT_RUN,
            "an upstream machine refusal must stop before effect accounting"
        );
        assert_eq!(
            audit.render_refusal(),
            Some(crate::DecompileRenderRefusal::MissingMachineProjectionAuthorization(
                crate::MachineProjectionRefusalOrigin::op_lowering(),
            )),
            "the production path must preserve the upstream machine authorization refusal"
        );
        assert!(
            !audit.output().contains("callother(") && !audit.output().contains("CPUID"),
            "opaque operations must not survive as executable helper-shaped C: {}",
            audit.output()
        );
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
            .op_to_stmt_impl(
                &SSAOp::CallInd {
                    target: make_var("X16", 0, 8),
                },
                &super::LowerFrame::for_expr(),
            )
            .expect("supported indirect-call lowering")
            .expect("fallback indirect call statement");

        assert_eq!(
            stmt,
            CStmt::Expr(CExpr::call(
                CExpr::External {
                    name: "sym_imp_printf".to_string(),
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
        let mut function =
            CFunction::new("invoke", CType::Void).with_body(vec![CStmt::Expr(callable)]);

        let reachable =
            crate::ast::strip_render_observations(&mut function, owner.expected_count())
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

        assert_eq!(
            ctx.op_to_stmt_with_args(
                &SSAOp::Call {
                    target: make_var("X16", 0, 8),
                },
                source_call.0,
                source_call.1,
            ),
            Err(OpLoweringRefusal::missing_machine_projection()),
            "typed callee identity alone must not authorize an executable source call",
        );
    }

    #[test]
    fn indirect_call_with_args_lowering_residualizes_typed_identity_without_callsite_facts() {
        let mut ctx = FoldingContext::new(64);
        let source_call = (0x1000, 0);
        install_indirect_callsite_identity(&mut ctx, source_call, "sym.imp.printf", None);

        assert_eq!(
            ctx.op_to_stmt_with_args(
                &SSAOp::CallInd {
                    target: make_var("X16", 0, 8),
                },
                source_call.0,
                source_call.1,
            ),
            Err(OpLoweringRefusal::missing_machine_projection()),
            "typed callee identity alone must not authorize an executable indirect source call",
        );
    }

    #[test]
    fn test_linear_addition_refuses_pointer_terms() {
        let ctx = FoldingContext::new(64);

        let expr = ctx.identity_simplify_binary(
            BinaryOp::Add,
            ctx.name_ref("buf"),
            CExpr::binary(BinaryOp::Add, ctx.name_ref("i"), ctx.name_ref("i")),
            Some(8),
        );

        assert_eq!(
            expr,
            CExpr::binary(
                BinaryOp::Add,
                ctx.name_ref("buf"),
                CExpr::binary(BinaryOp::Add, ctx.name_ref("i"), ctx.name_ref("i"))
            ),
            "pointer arithmetic must not be reordered or collapsed by scalar linear normalization"
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
                return_type: CType::Int { bits: 32, signedness: r2types::Signedness::Signed },
                params: Vec::new(),
                variadic: false,
            }),
        );

        let poisoned_rendered_call = CExpr::call(
            CExpr::External {
                name: "sym_imp_free".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            },
            vec![ctx.name_ref("ptr")],
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
                name: "sym_local_rendered_name".to_string(),
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
    fn should_inline_requires_the_exact_sealed_disposition() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(7, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(0x30, 8),
            src: Varnode::register(0, 8),
        });
        entry.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::unique(0x10, 8),
            b: Varnode::unique(0x30, 8),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2000, 8),
            val: Varnode::unique(0x20, 8),
        });
        // The sum is read twice and reads a register, so the plan binds it,
        // and the test needs one value the plan inlines and one it does not.
        // Both conditions are load-bearing: a value with one reader is folded
        // into that reader, and a value that reads nothing but literals is
        // spelled at every reader it has.
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2008, 8),
            val: Varnode::unique(0x20, 8),
        });
        let prepared =
            prepared_from_r2il_blocks(&[entry], &arch).with_name("sealed_inline_admission");
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let SSAOp::Copy { src, .. } = &block.ops[0] else {
            panic!("fixture must begin with a copy");
        };
        let SSAOp::IntAdd { dst, .. } = &block.ops[2] else {
            panic!("fixture must add the register to the literal");
        };
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (plan, names, _) = install_observed_lowering(&mut ctx, &prepared);
        let src_value = prepared
            .graph()
            .value_id_for_var(src)
            .expect("constant source value");
        let dst_value = prepared
            .graph()
            .value_id_for_var(dst)
            .expect("sum destination value");

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
        ctx.inlined_renderings
            .borrow_mut()
            .insert(src.display_name(), CExpr::IntLit(99));
        ctx.inlined_renderings
            .borrow_mut()
            .insert(dst.display_name(), CExpr::IntLit(100));
        // The literal is marked: an inlined value owes its own cell wherever
        // it renders, and the marker is how the accounting finds it.
        assert_eq!(
            ctx.get_expr(src).map(|expr| expr.unobserved().clone()),
            Ok(CExpr::IntLit(7))
        );
        assert_eq!(
            ctx.get_expr(dst),
            Ok(CExpr::Var(
                names
                    .symbol_for_value(dst_value)
                    .expect("bound destination symbol")
            ))
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
    fn assignment_without_exact_elision_keeps_write_and_rhs_occurrence() {
        let ctx = FoldingContext::new(64);
        let lhs = ctx.name_ref("x");
        let plain = ctx
            .assign_stmt(lhs.clone(), ctx.name_ref("x"))
            .expect("spelling alone cannot prove that an assignment is dead");
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (rhs_id, observed_rhs) = owner
            .observe_expr(ctx.name_ref("x"))
            .expect("assignment observation");
        let marked = ctx
            .assign_stmt(lhs, observed_rhs)
            .expect("an observed RHS must not be suppressed by its spelling");
        let mut function = CFunction::new("assign", CType::Void).with_body(vec![marked]);
        let reachable =
            crate::ast::strip_render_observations(&mut function, owner.expected_count())
                .expect("the RHS occurrence must survive exactly once");

        assert!(reachable.contains(rhs_id));
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
        let (use_id, observed_rhs) = owner.observe_expr(rhs).expect("pointer RHS observation");
        let marked = ctx
            .assign_stmt(ctx.name_ref("arg1"), observed_rhs)
            .expect("metadata must not hide a pointer-shaped RHS");
        let mut function = CFunction::new("assign", CType::Void).with_body(vec![marked]);
        let reachable =
            crate::ast::strip_render_observations(&mut function, owner.expected_count())
                .expect("the pointer observation must survive exactly once");

        assert!(reachable.contains(use_id));
        assert_eq!(function.body, vec![plain]);
    }

    #[test]
    fn a_conversion_is_observation_transparent() {
        let ctx = FoldingContext::new(64);
        let target = CType::Int { bits: 32, signedness: r2types::Signedness::Signed };
        let source = r2rewrite::CValue::Typed(CType::Int {
            bits: 64,
            signedness: r2types::Signedness::Unsigned,
        });
        let value = ctx.name_ref("value");
        let plain = ctx.convert(value.clone(), &source, &target);
        assert!(matches!(plain, CExpr::Cast { .. }), "a narrowing is spelled");
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (use_id, observed) = owner.observe_expr(value).expect("value observation");
        let marked = ctx.convert(observed, &source, &target);
        let mut function = CFunction::new("cast", CType::Void).with_body(vec![CStmt::Expr(marked)]);
        let reachable =
            crate::ast::strip_render_observations(&mut function, owner.expected_count())
                .expect("the value observation must survive exactly once");

        assert!(reachable.contains(use_id));
        assert_eq!(function.body, vec![CStmt::Expr(plain)]);
    }

    #[test]
    fn typed_literal_rewrite_is_observation_transparent() {
        let ctx = FoldingContext::new(64);
        let target = CType::Int { bits: 8, signedness: r2types::Signedness::Signed };
        let literal = CExpr::UIntLit(255);
        // A constant is spelled in the type that reads it rather than cast
        // to it, so the conversion of a constant is a respelling.
        let plain = ctx.convert(literal.clone(), &r2rewrite::CValue::Constant, &target);
        let mut owner = crate::ast::RenderObservationOwner::new();
        let (use_id, observed) = owner.observe_expr(literal).expect("literal observation");
        let marked = ctx.convert(observed, &r2rewrite::CValue::Constant, &target);
        let mut function =
            CFunction::new("literal", CType::Void).with_body(vec![CStmt::Expr(marked)]);
        let reachable =
            crate::ast::strip_render_observations(&mut function, owner.expected_count())
                .expect("the literal observation must survive exactly once");

        assert!(reachable.contains(use_id));
        assert_eq!(plain, CExpr::IntLit(-1));
        assert_eq!(function.body, vec![CStmt::Expr(plain)]);
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
            CExpr::binary(BinaryOp::BitOr, ctx.name_ref("x"), CExpr::IntLit(1))
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
                name: "sym_imp_fact_helper".to_string(),
                kind: crate::symbol::ExternalKind::Import,
            })
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
    fn certified_call_args_refuse_without_binding_plan_spelling() {
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

        let prepared = prepared_from_r2il_blocks_with_call_arguments(&[entry], &arch, 1)
            .with_name("call_arg_without_spelling_authority");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_certified_function_facts(&mut ctx);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        install_callsite_resolution(&mut ctx, (0x1000, 2), 0x401050, "sym.helper", None);

        let block = prepared.function().get_block(0x1000).expect("entry");
        enter_exact_test_site(&ctx, block.addr, 2);
        assert_eq!(
            ctx.op_to_stmt_with_args(&block.ops[2], block.addr, 2),
            Err(OpLoweringRefusal::missing_machine_projection()),
            "a certified position without binding-plan spelling authority must refuse the call"
        );
    }

    #[test]
    fn certified_call_args_take_spelling_only_from_binding_plan() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0x10, 8),
            src: Varnode::constant(7, 8),
        });
        entry.push(R2ILOp::IntZExt {
            dst: Varnode::register(0x18, 8),
            src: Varnode::unique(0x200, 4),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(1, 8),
            src: Varnode::constant(0x401050, 8),
        });
        entry.push(R2ILOp::Call {
            target: Varnode::unique(1, 8),
        });

        let prepared = prepared_from_r2il_blocks_with_call_arguments(&[entry], &arch, 2)
            .with_name("certified_call_arg");
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        install_certified_function_facts(&mut ctx);
        ctx.set_function_names(HashMap::from([(0x401050, "sym.helper".to_string())]));
        install_callsite_resolution(&mut ctx, (0x1000, 3), 0x401050, "sym.helper", None);

        let argument_values = prepared
            .callsite_certificate_for_op(0x1000, 3)
            .expect("prepared callsite certificate")
            .argument_values
            .clone();
        assert_eq!(argument_values.len(), 2);
        assert!(
            !ctx.inputs
                .function_facts
                .render_facts()
                .expression_is_renderable(argument_values[1]),
            "the fixture must expose the expression-certificate disagreement"
        );

        let block = prepared.function().get_block(0x1000).expect("entry");
        let (_plan, names, _journal) = install_observed_lowering(&mut ctx, &prepared);
        for value in &argument_values {
            assert!(
                matches!(
                    names.require_value(*value),
                    Ok(crate::binding_plan::PlannedValueSymbol::Bound(_)
                        | crate::binding_plan::PlannedValueSymbol::Inline(_))
                ),
                "the sealed binding plan must authorize argument {value:?}"
            );
        }

        let mut prepared_view = crate::analysis::PreparedSemanticView::build_with_bindings(
            &ctx.symbols,
            crate::analysis::PreparedSemanticViewInputs {
                prepared: &prepared,
                stack_slots: ctx.inputs.stack_slots,
                visible_bindings: ctx.inputs.visible_bindings,
                function_facts: ctx.inputs.function_facts,
                certified_rendering_required: false,
            },
            Rc::clone(names),
        )
        .expect("prepared semantic view");
        let call_view = prepared_view
            .call_view_by_site
            .get_mut(&(0x1000, 3))
            .expect("prepared call view");
        assert_eq!(call_view.authoritative_arg_values, argument_values);
        call_view.authoritative_args.truncate(1);
        call_view.authoritative_arg_values.truncate(1);
        ctx.inputs.prepared_semantic_view = Some(Box::leak(Box::new(prepared_view)));

        enter_exact_test_site(&ctx, block.addr, 3);
        let stmt = ctx
            .op_to_stmt_with_args(&block.ops[3], block.addr, 3)
            .expect("supported call lowering")
            .expect("call stmt");

        let CStmt::Expr(CExpr::Call { func, args, .. }) = stmt.unobserved() else {
            panic!("expected certified call expression, got {stmt:?}");
        };
        assert_eq!(
            func.unobserved(),
            &CExpr::External {
                name: "sym_helper".to_string(),
                kind: crate::symbol::ExternalKind::Function,
            }
        );
        // The argument is a read of the value the callsite certificate names,
        // spelled by the binding plan and marked as a read. Spelling it from
        // the operation that defined the value instead would re-evaluate a
        // definition the plan has already bound, and would name a binding this
        // statement is not authorized to read.
        assert_eq!(args.len(), 2, "the cached one-argument view cannot truncate the call");
        for (argument, value) in args.iter().zip(argument_values) {
            let expected = ctx
                .planned_value_expr(value)
                .expect("the plan spells every certified argument value");
            // Through the markers, not around them. Asking the plan a second
            // time allocates fresh observation ids, so two spellings of one
            // value are equal as expressions and unequal as trees.
            assert!(
                argument.transparently_eq(&expected),
                "argument {argument:?} is not the plan's spelling {expected:?}"
            );
            assert!(
                matches!(argument, CExpr::Observed { .. }),
                "a bound call argument is a read and must carry its read marker: {argument:?}"
            );
        }
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
            target: Varnode::register(0x30, 8),
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
        let transition_sites = prepared
            .obligations()
            .obligations()
            .values()
            .filter(|obligation| {
                obligation.id.kind == r2ssa::SemanticObligationKind::LiveStateTransition
            })
            .filter_map(|obligation| obligation.edge_use)
            .collect::<BTreeSet<_>>();
        assert!(
            !transition_sites.is_empty(),
            "fixture must retain an exact loop-transition edge"
        );
        let (block_addr, synthetic_idx, shifted_idx, shifted_inst) = graph
            .block_order
            .iter()
            .find_map(|block_id| {
                let block_addr = graph.block(*block_id)?.addr;
                let block = normalized.get_block(block_addr)?;
                let synthetic_idx = (0..block.ops.len()).find(|op_idx| {
                    let site = crate::normalize::NormalizedOpSite {
                        block: *block_id,
                        op_idx: *op_idx,
                    };
                    matches!(
                        origins.origin(site),
                        Some(crate::normalize::NormalizedOpOrigin::PhiEdgeCopy(_))
                            | Some(crate::normalize::NormalizedOpOrigin::RelocatedInitializer(
                                _
                            ))
                    ) && origins
                        .projection(site, &prepared)
                        .ok()
                        .flatten()
                        .is_some_and(|projection| {
                            projection.inputs.iter().any(|input| {
                                input
                                    .uses
                                    .iter()
                                    .any(|site| transition_sites.contains(site))
                            })
                        })
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
        let synthetic_source_uses = origins
            .projection(
                crate::normalize::NormalizedOpSite {
                    block: graph
                        .block_id_for_addr(block_addr)
                        .expect("normalized block has a source graph identity"),
                    op_idx: synthetic_idx,
                },
                &prepared,
            )
            .expect("normalization projection is authority-bound")
            .expect("synthetic phi operation has an exact source projection")
            .inputs
            .iter()
            .flat_map(|input| input.uses.iter().copied())
            .collect::<BTreeSet<_>>();

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
            !synthetic_obligations.is_empty()
                && synthetic_obligations.iter().all(|id| {
                    id.kind == r2ssa::SemanticObligationKind::LiveStateTransition
                        && matches!(id.instruction.site, r2ssa::CanonicalInstructionSite::Phi(_))
                        && prepared
                            .obligations()
                            .obligations()
                            .get(id)
                            .and_then(|obligation| obligation.edge_use)
                            .is_some_and(|site| synthetic_source_uses.contains(&site))
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
        let prepared =
            prepared_from_r2il_blocks(&[entry], &arch).with_name("exact_memory_obligation_proof");
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

    /// Property 3: the rendering does not depend on the order the input
    /// arrives in.
    ///
    /// Blocks are keyed by address, so permuting the slice they are handed in
    /// describes the same function. Anything that reaches the output from an
    /// unordered container, or from the order blocks happened to be visited in,
    /// shows up here as a byte difference between two renderings of one
    /// function. The plan states this property and until now nothing proved it.
    #[test]
    fn rendering_does_not_depend_on_input_block_order() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1000, 0x10);
        entry.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(1, 8),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1020, 8),
            cond: Varnode::register(0x38, 8),
        });
        let mut middle = R2ILBlock::new(0x1010, 0x10);
        middle.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::register(0x38, 8),
        });
        let mut exit = R2ILBlock::new(0x1020, 0x10);
        exit.push(R2ILOp::IntXor {
            dst: Varnode::register(0x10, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(7, 8),
        });
        let blocks = [entry, middle, exit];

        let render = |order: &[usize]| -> String {
            let permuted = order
                .iter()
                .map(|index| blocks[*index].clone())
                .collect::<Vec<_>>();
            let fixture = prepared_from_r2il_blocks(&permuted, &arch).with_name("determinism");
            let decompiler = crate::Decompiler::new(crate::DecompilerConfig::default());
            decompiler.decompile_input(&crate::DecompilerInput::new(fixture.facts))
        };

        // The entry is whichever block comes first, so it stays first: moving it
        // would describe a different function rather than the same one in a
        // different order.
        let canonical = render(&[0, 1, 2]);
        assert_eq!(
            canonical,
            render(&[0, 2, 1]),
            "input block order changed the rendering"
        );
    }

    #[test]
    fn rendered_integer_division_owns_its_exact_trap_obligation() {
        let arch = make_test_arch_x86_64();
        let mut entry = R2ILBlock::new(0x1910, 4);
        // The dividend is the incoming register, not a literal. A division of
        // two constants is folded to its result before rendering, and then
        // there is no division left to own the obligation this test is about.
        entry.push(R2ILOp::IntDiv {
            dst: Varnode::register(0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(3, 8),
        });
        let prepared = prepared_from_r2il_blocks(&[entry], &arch)
            .with_name("rendered_integer_division_trap");
        let block = prepared.function().get_block(0x1910).expect("entry");
        let op_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::IntDiv { .. }))
            .expect("division operation");
        let inst = prepared
            .graph()
            .inst_id_for_op_site(block.addr, op_idx)
            .expect("division graph instruction");
        let value = prepared
            .graph()
            .inst(inst)
            .and_then(|inst| inst.output)
            .expect("division output");
        let ctx = make_x86_64_ctx_with_prepared(&prepared);

        let obligations = ctx.exact_effect_obligations_for_normalized_value(
            EffectOccurrenceKind::Expression,
            block.addr,
            op_idx,
            Some(value),
        );

        assert!(obligations.iter().any(|id| {
            id.kind == r2ssa::SemanticObligationKind::Trap
                && prepared
                    .obligations()
                    .instruction_for_inst(inst)
                    .is_some_and(|instruction| id.instruction == instruction.id)
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
    fn prepared_runtime_analysis_refuses_without_exact_source_artifact() {
        let mut ctx = FoldingContext::new(64);
        let execution = r2ssa::SsaExecutionControl::default();
        let control =
            crate::DecompileWorkControl::new(&execution, crate::DecompileWorkPhase::Structuring);

        assert_eq!(
            ctx.analyze_blocks_with_control(&[], control),
            Err(crate::analysis::PreparedRuntimeFactsError::Lowering(
                OpLoweringRefusal::missing_machine_projection(),
            )),
            "missing exact SSA authority must be a typed refusal, never an empty analysis"
        );
    }

    #[test]
    fn certified_member_fact_does_not_bypass_the_address_binding_plan() {
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
        // The member address is read twice, so it keeps a binding. Read once
        // it would fold into the load, and the plan this test checks would
        // have no address value to answer for. The second read stores the
        // address rather than loading through it, so the aggregate access
        // this test counts stays the single one the load makes.
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x3000, 8),
            val: Varnode::unique(0x100, 8),
        });
        let prepared =
            prepared_x86_with_demo_struct_parameter(&[entry], &arch).with_name("field_with_cert");
        let interface = prepared
            .machine_context()
            .function_interface()
            .expect("source-owned function interface");
        let projections = prepared
            .aggregate_accesses()
            .projections_for_revision(interface.revision_identity())
            .expect("aggregate projections for the exact source revision");
        assert_eq!(projections.len(), 1);
        assert_eq!(
            projections
                .values()
                .next()
                .map(|fact| fact.member_name.as_ref()),
            Some("hash")
        );
        assert!(
            prepared
                .function_facts()
                .type_facts()
                .field_access_certificates
                .iter()
                .any(|fact| fact.slot == 0 && fact.field_offset == 8 && fact.field_name == "hash"),
            "source aggregate projection must reach the canonical type certificate: {:?}",
            prepared
                .function_facts()
                .type_facts()
                .field_access_certificates
        );
        assert!(matches!(
            prepared
                .function_facts()
                .render()
                .and_then(|render| {
                    render
                        .certified_entities
                        .get(&r2ssa::SemanticId::Parameter(0))
                }),
            Some(r2types::CertifiedEntity::Parameter {
                ty: Some(r2types::CTypeLike::Pointer(inner)),
                ..
            }) if matches!(inner.as_ref(), r2types::CTypeLike::Struct(name) if name == "DemoStruct")
        ));
        let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
        let (_plan, names, _journal) = install_observed_lowering(&mut ctx, &prepared);
        enter_exact_test_site(&ctx, 0x1000, 1);
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let SSAOp::Load { dst, addr, .. } = &block.ops[1] else {
            panic!("fixture load must remain at its exact source site");
        };
        let memory = ctx
            .certified_memory_access_for_current_op(false)
            .expect("source-owned memory render fact");
        let member = ctx
            .inputs
            .render_facts()
            .and_then(|facts| {
                facts
                    .member_accesses_by_op
                    .get(&(memory.block_addr, memory.op_index, false))
            })
            .and_then(|facts| facts.iter().find(|fact| fact.access == memory.access))
            .expect("source-owned field access certificate");
        assert_eq!(member.field_name, "hash");
        let (_, address_expr) = ctx
            .certified_memory_address_expr(memory)
            .expect("source-owned address expression");
        let address_symbol = names
            .symbol_for_value(memory.address)
            .expect("the exact address value has one sealed binding");
        // The address is marked as the read it is, so the expression is the
        // binding's symbol under an observation marker rather than a bare
        // variable. What the test is about is unchanged: the address comes from
        // the sealed binding and not from a bypass.
        assert!(matches!(address_expr, CExpr::Observed { .. }));
        assert_eq!(*address_expr.unobserved(), CExpr::Var(address_symbol));
        let access = ctx
            .render_certified_load_access_expr(dst, addr, CType::Int { bits: 64, signedness: r2types::Signedness::Unsigned })
            .expect("exact memory and field facts must render");
        assert_eq!(access.access(), memory.access);
        let expr = access.expr();

        assert!(
            matches!(expr, CExpr::Deref(_)),
            "a field label without a base-identity contract must retain the exact address binding: {expr:?}"
        );
    }
    #[test]
    fn forged_block_assumption_cannot_replace_the_exact_branch_use() {
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
        assert_eq!(
            ctx.prepared_predicate_candidate_for_branch_block_for_test(0x5000, &cond),
            None,
            "a comparison fact whose condition ValueId does not own the terminal branch UseSite must refuse"
        );
    }
}
