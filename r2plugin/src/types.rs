use crate::blocks::BlockSlice;
use crate::context::{PluginCtxView, require_ctx_view};
#[cfg(test)]
use crate::{InferredParamJson, InferredSignatureCcJson};
use crate::{R2ILBlock, R2ILContext};
use std::os::raw::c_char;
use std::ptr;

pub(crate) struct FunctionInput<'a> {
    pub(crate) ctx: PluginCtxView<'a>,
    pub(crate) blocks: BlockSlice,
}

#[cfg(test)]
fn type_like_to_string(ty: &r2types::CTypeLike) -> String {
    r2types::render_c_type_like(ty)
}

#[cfg(test)]
pub(crate) type VarProt = r2types::RecoveredVariable;
#[cfg(test)]
pub(crate) type TypeHintRank = r2types::TypeHintRank;
#[cfg(test)]
pub(crate) type TypeHint = r2types::TypeHint;

pub(crate) fn build_function_input<'a>(
    ctx: *const R2ILContext,
    blocks: *const *const crate::R2ILBlock,
    num_blocks: usize,
) -> Option<FunctionInput<'a>> {
    let ctx = require_ctx_view(ctx)?;
    let blocks = unsafe { BlockSlice::from_ffi(blocks, num_blocks)? };
    Some(FunctionInput { ctx, blocks })
}

#[cfg(test)]
fn apply_signature_context_overrides(
    sig: &mut InferredSignatureCcJson,
    signature: Option<&r2types::FunctionSignatureSpec>,
) -> (
    std::collections::HashMap<usize, String>,
    std::collections::HashMap<usize, String>,
) {
    let mut param_types = std::collections::HashMap::new();
    let mut param_names = std::collections::HashMap::new();

    if let Some(signature) = signature {
        while sig.params.len() < signature.params.len() {
            let idx = sig.params.len();
            let param_type = signature
                .params
                .get(idx)
                .and_then(|param| param.ty.as_ref())
                .map(type_like_to_string)
                .unwrap_or_else(|| "void *".to_string());
            sig.params.push(InferredParamJson {
                name: format!("arg{}", idx + 1),
                param_type,
            });
        }
        if let Some(ret_ty) = signature.ret_type.as_ref()
            && !matches!(ret_ty, r2types::CTypeLike::Unknown)
        {
            let ret_ty_str = type_like_to_string(ret_ty);
            sig.ret_type = ret_ty_str;
        }
        for (idx, param) in signature.params.iter().enumerate() {
            if let Some(ty) = param.ty.as_ref() {
                let ty_str = type_like_to_string(ty);
                param_types.insert(idx, ty_str.clone());
                if !matches!(ty, r2types::CTypeLike::Unknown)
                    && let Some(inferred_param) = sig.params.get_mut(idx)
                {
                    inferred_param.param_type = ty_str;
                }
            }
            if !crate::is_generic_arg_name(&param.name) {
                param_names.insert(idx, param.name.clone());
                if let Some(inferred_param) = sig.params.get_mut(idx) {
                    inferred_param.name = param.name.clone();
                }
            }
        }
        sig.signature = crate::format_afs_signature(&sig.function_name, &sig.ret_type, &sig.params);
        sig.confidence = sig.confidence.max(signature_strength(signature));
    }

    (param_types, param_names)
}

#[cfg(test)]
pub(crate) fn apply_main_signature_override(
    function_name: &str,
    signature_cc: &mut InferredSignatureCcJson,
    merged_signature: &mut Option<r2types::FunctionSignatureSpec>,
) {
    let mut canonicalized = merged_signature.clone();
    if !r2types::apply_main_signature_override(function_name, &mut canonicalized) {
        return;
    }

    let Some(main_signature) = canonicalized else {
        return;
    };
    signature_cc.ret_type = main_signature
        .ret_type
        .as_ref()
        .map(type_like_to_string)
        .unwrap_or_else(|| "int32_t".to_string());
    signature_cc.params = main_signature
        .params
        .iter()
        .map(|param| InferredParamJson {
            name: param.name.clone(),
            param_type: param
                .ty
                .as_ref()
                .map(type_like_to_string)
                .unwrap_or_else(|| "void *".to_string()),
        })
        .collect();
    signature_cc.signature = crate::format_afs_signature(
        &signature_cc.function_name,
        &signature_cc.ret_type,
        &signature_cc.params,
    );
    signature_cc.confidence = signature_cc.confidence.max(96);
    *merged_signature = Some(main_signature);
}

#[cfg(test)]
fn signature_strength(signature: &r2types::FunctionSignatureSpec) -> u8 {
    let has_type_info =
        signature.ret_type.is_some() || signature.params.iter().any(|param| param.ty.is_some());
    let has_named_params = signature
        .params
        .iter()
        .any(|param| !crate::is_generic_arg_name(&param.name));
    if has_type_info || has_named_params {
        96
    } else {
        80
    }
}

#[cfg(test)]
#[derive(Debug)]
pub(crate) struct DataRef {
    pub(crate) from: u64,
    pub(crate) to: u64,
    pub(crate) space: r2il::SpaceId,
    pub(crate) ref_type: String,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighDataRef {
    from: u64,
    to: u64,
    space_kind: u32,
    custom_space: u32,
    ref_kind: c_char,
}

pub struct R2SleighDataRefs {
    refs: Vec<R2SleighDataRef>,
}

const FFI_DATA_REF_SPACE_RAM: u32 = 0;
const FFI_DATA_REF_SPACE_REGISTER: u32 = 1;
const FFI_DATA_REF_SPACE_UNIQUE: u32 = 2;
const FFI_DATA_REF_SPACE_CONST: u32 = 3;
const FFI_DATA_REF_SPACE_CUSTOM: u32 = 4;

#[cfg(test)]
fn data_ref_from_fact(fact: &r2ssa::DataRefFact) -> DataRef {
    DataRef {
        from: fact.from,
        to: fact.to,
        space: fact.space,
        ref_type: fact.kind.as_str().to_string(),
    }
}

fn ffi_data_ref_space(space: r2il::SpaceId) -> (u32, u32) {
    match space {
        r2il::SpaceId::Ram => (FFI_DATA_REF_SPACE_RAM, 0),
        r2il::SpaceId::Register => (FFI_DATA_REF_SPACE_REGISTER, 0),
        r2il::SpaceId::Unique => (FFI_DATA_REF_SPACE_UNIQUE, 0),
        r2il::SpaceId::Const => (FFI_DATA_REF_SPACE_CONST, 0),
        r2il::SpaceId::Custom(id) => (FFI_DATA_REF_SPACE_CUSTOM, id),
    }
}

fn ffi_data_refs_from_refs(refs: &[r2ssa::DataRefFact]) -> R2SleighDataRefs {
    R2SleighDataRefs {
        refs: refs
            .iter()
            .map(|reference| {
                let (space_kind, custom_space) = ffi_data_ref_space(reference.space);
                R2SleighDataRef {
                    from: reference.from,
                    to: reference.to,
                    space_kind,
                    custom_space,
                    ref_kind: reference.kind.as_char() as c_char,
                }
            })
            .collect(),
    }
}

#[cfg(test)]
pub(crate) fn merge_type_hint(
    hints: &mut std::collections::HashMap<String, TypeHint>,
    key: String,
    incoming: TypeHint,
) {
    r2types::merge_type_hint(hints, key, incoming);
}

#[cfg(test)]
pub(crate) const X86_ARG_REGS: &[(&str, &[&str])] = r2types::X86_ARG_REGS;
#[cfg(test)]
pub(crate) const X86_FRAME_BASES: &[&str] = r2types::X86_FRAME_BASES;
#[cfg(test)]
type ArgAliasMap = r2types::ArgAliasMap;

#[cfg(test)]
pub(crate) fn ssa_var_block_key(block_addr: u64, var: &r2ssa::SSAVar) -> String {
    r2types::ssa_var_block_key(block_addr, var)
}

#[cfg(test)]
pub(crate) fn scalar_register_family_key(name: &str) -> String {
    r2types::scalar_register_family_key(name)
}

#[cfg(test)]
pub(crate) fn collect_signature_type_evidence_context(
    ssa_blocks: &[r2ssa::SSABlock],
) -> r2types::SignatureTypeEvidenceContext {
    r2types::collect_signature_type_evidence_context(ssa_blocks)
}

#[cfg(test)]
pub(crate) fn merge_register_type_hints(
    metadata_hints: &std::collections::HashMap<String, TypeHint>,
    usage_hints: &std::collections::HashMap<String, TypeHint>,
    arg_regs: ArgAliasMap,
) -> std::collections::HashMap<String, TypeHint> {
    let mut merged = std::collections::HashMap::new();

    for (reg, hint) in metadata_hints {
        merge_type_hint(&mut merged, reg.clone(), hint.clone());
    }
    for (reg, hint) in usage_hints {
        merge_type_hint(&mut merged, reg.clone(), hint.clone());
    }

    for (canonical, aliases) in arg_regs {
        let candidates: Vec<TypeHint> = std::iter::once(*canonical)
            .chain(aliases.iter().copied())
            .filter_map(|name| merged.get(name).cloned())
            .collect();
        if let Some(best) = candidates
            .into_iter()
            .max_by(|a, b| a.rank.cmp(&b.rank).then_with(|| b.ty.cmp(&a.ty)))
        {
            merge_type_hint(&mut merged, (*canonical).to_string(), best.clone());
            for alias in *aliases {
                merge_type_hint(&mut merged, alias.to_string(), best.clone());
            }
        }
    }

    merged
}

#[cfg(test)]
pub(crate) fn add_stack_var(
    vars: &mut Vec<VarProt>,
    seen_slots: &mut std::collections::HashMap<(bool, i64), usize>,
    base_reg: &str,
    frame_bases: &[&str],
    offset: i64,
    size: u32,
    type_override: Option<String>,
) {
    let is_frame_base = frame_bases.contains(&base_reg);
    let slot_key = (is_frame_base, offset);
    if let Some(existing_idx) = seen_slots.get(&slot_key).copied() {
        if let Some(override_ty) = type_override
            && override_ty == "void *"
            && let Some(existing) = vars.get_mut(existing_idx)
            && existing.var_type != "void *"
        {
            existing.var_type = override_ty;
        }
        return;
    }

    let is_arg = if is_frame_base { offset > 0 } else { false };

    let var_name = if is_arg && offset > 8 {
        format!("arg_{:x}h", offset.unsigned_abs())
    } else {
        format!("var_{:x}h", offset.unsigned_abs())
    };

    let kind = if is_frame_base { "b" } else { "s" };

    vars.push(VarProt {
        name: var_name,
        kind: kind.to_string(),
        delta: offset,
        var_type: type_override.unwrap_or_else(|| size_to_type(size)),
        isarg: is_arg && offset > 8,
        reg: None,
    });
    seen_slots.insert(slot_key, vars.len().saturating_sub(1));
}

#[cfg(test)]
pub(crate) fn parse_const_value(name: &str) -> Option<u64> {
    r2ssa::parse_const_value(name)
}

#[cfg(test)]
pub(crate) fn size_to_type(size: u32) -> String {
    r2types::size_to_type(size)
}

fn data_refs_for_ffi(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    _fcn_addr: u64,
) -> Option<Vec<r2ssa::DataRefFact>> {
    let input = build_function_input(ctx, blocks, num_blocks)?;
    r2ssa::data_refs_from_blocks(input.blocks.as_slice(), input.ctx.arch)
}

pub(crate) fn r2sleigh_data_refs_typed(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
) -> *mut R2SleighDataRefs {
    let Some(refs) = data_refs_for_ffi(ctx, blocks, num_blocks, fcn_addr) else {
        return ptr::null_mut();
    };
    Box::into_raw(Box::new(ffi_data_refs_from_refs(&refs)))
}

pub(crate) fn r2sleigh_data_refs_items(
    refs: *const R2SleighDataRefs,
    count: *mut usize,
) -> *const R2SleighDataRef {
    if refs.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let refs = unsafe { &*refs };
    if !count.is_null() {
        unsafe {
            *count = refs.refs.len();
        }
    }
    refs.refs.as_ptr()
}

pub(crate) fn r2sleigh_data_refs_free(refs: *mut R2SleighDataRefs) {
    if !refs.is_null() {
        unsafe {
            drop(Box::from_raw(refs));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        TypeEvidence, collect_type_evidence_for_var, infer_signature_return_type,
        resolve_evidence_driven_type,
    };

    fn signed_type(bits: u32) -> r2types::CTypeLike {
        r2types::CTypeLike::Int {
            bits,
            signedness: r2types::Signedness::Signed,
        }
    }

    fn void_ptr_type() -> r2types::CTypeLike {
        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Void))
    }

    #[test]
    fn name_only_summary_report_rejects_resolved_name_without_typed_linkage() {
        let raw = r2ssa::FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x4b30),
            Some("fcn.00004b30".to_string()),
        );
        assert!(
            r2sym::compile_named_native_worker_summary_report(&raw, true).is_none(),
            "an autogenerated raw name should not invent advisory semantics"
        );

        let resolved = r2ssa::FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x4b30),
            Some("readlinebuffer_delim".to_string()),
        );
        assert!(
            r2sym::compile_named_native_worker_summary_report(&resolved, true).is_none(),
            "a resolved display name without typed imported linkage must remain advisory-only"
        );
    }

    #[test]
    fn ffi_data_refs_preserve_exact_address_space_tags() {
        let refs = ffi_data_refs_from_refs(&[
            r2ssa::DataRefFact {
                from: 0x1000,
                to: 0x2000,
                kind: r2ssa::DataRefKind::Data,
                space: r2il::SpaceId::Ram,
            },
            r2ssa::DataRefFact {
                from: 0x1004,
                to: 0x2000,
                kind: r2ssa::DataRefKind::Data,
                space: r2il::SpaceId::Register,
            },
            r2ssa::DataRefFact {
                from: 0x1008,
                to: 0x2000,
                kind: r2ssa::DataRefKind::Data,
                space: r2il::SpaceId::Unique,
            },
            r2ssa::DataRefFact {
                from: 0x100c,
                to: 0x2000,
                kind: r2ssa::DataRefKind::Data,
                space: r2il::SpaceId::Const,
            },
            r2ssa::DataRefFact {
                from: 0x1010,
                to: 0x2000,
                kind: r2ssa::DataRefKind::Data,
                space: r2il::SpaceId::Custom(0),
            },
            r2ssa::DataRefFact {
                from: 0x1014,
                to: 0x2000,
                kind: r2ssa::DataRefKind::Data,
                space: r2il::SpaceId::Custom(7),
            },
        ]);

        let tags = refs
            .refs
            .iter()
            .map(|reference| (reference.space_kind, reference.custom_space))
            .collect::<Vec<_>>();
        assert_eq!(tags, vec![(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (4, 7)]);
    }

    #[test]
    fn ffi_data_ref_layout_matches_the_private_c_query_payload() {
        assert_eq!(std::mem::offset_of!(R2SleighDataRef, from), 0);
        assert_eq!(std::mem::offset_of!(R2SleighDataRef, to), 8);
        assert_eq!(std::mem::offset_of!(R2SleighDataRef, space_kind), 16);
        assert_eq!(std::mem::offset_of!(R2SleighDataRef, custom_space), 20);
        assert_eq!(std::mem::offset_of!(R2SleighDataRef, ref_kind), 24);
        assert!(matches!(std::mem::size_of::<R2SleighDataRef>(), 28 | 32));
    }

    #[test]
    fn signature_context_overrides_extend_empty_param_list() {
        let mut sig = InferredSignatureCcJson {
            function_name: "main".to_string(),
            signature: "int32_t main(void)".to_string(),
            ret_type: "int32_t".to_string(),
            params: Vec::new(),
            callconv: String::new(),
            arch: "aarch64".to_string(),
            confidence: 80,
            callconv_confidence: 0,
        };
        let merged = Some(r2types::FunctionSignatureSpec {
            ret_type: Some(r2types::CTypeLike::Int {
                bits: 32,
                signedness: r2types::Signedness::Signed,
            }),
            params: vec![
                r2types::FunctionParamSpec {
                    name: "argc".to_string(),
                    ty: Some(r2types::CTypeLike::Int {
                        bits: 32,
                        signedness: r2types::Signedness::Signed,
                    }),
                },
                r2types::FunctionParamSpec {
                    name: "argv".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Int {
                            bits: 8,
                            signedness: r2types::Signedness::Signed,
                        })),
                    ))),
                },
            ],
        });

        apply_signature_context_overrides(&mut sig, merged.as_ref());

        assert_eq!(sig.params.len(), 2);
        assert_eq!(sig.params[0].name, "argc");
        assert_eq!(sig.params[0].param_type, "int32_t");
        assert_eq!(sig.params[1].name, "argv");
        assert_eq!(sig.params[1].param_type, "int8_t**");
    }

    #[test]
    fn scalar_register_family_key_merges_arm64_x_and_w_aliases() {
        assert_eq!(scalar_register_family_key("X0"), "aarch64:gpr:0");
        assert_eq!(scalar_register_family_key("w0"), "aarch64:gpr:0");
        assert_eq!(scalar_register_family_key("fp"), "aarch64:gpr:29");
        assert_eq!(scalar_register_family_key("lr"), "aarch64:gpr:30");
    }

    #[test]
    fn scalar_width_hints_narrow_arm64_x_family_from_w_family_usage() {
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("W8", 1, 4),
                    src: r2ssa::SSAVar::new("W0", 0, 4),
                },
                r2ssa::SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    src: r2ssa::SSAVar::new("W8", 1, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("X10", 1, 8),
                    a: r2ssa::SSAVar::new("X0", 0, 8),
                    b: r2ssa::SSAVar::new("const:1", 0, 8),
                },
            ],
        }];

        let evidence = collect_signature_type_evidence_context(&blocks);
        assert_eq!(
            evidence.width_bits.get("x0_0"),
            Some(&32),
            "{:?}",
            evidence.width_bits
        );
        assert_eq!(
            evidence.width_bits.get("x9_1"),
            Some(&32),
            "{:?}",
            evidence.width_bits
        );
        assert_eq!(
            evidence.width_bits.get("x10_1"),
            Some(&32),
            "{:?}",
            evidence.width_bits
        );
    }

    #[test]
    fn main_signature_override_is_canonical_and_caps_extra_params() {
        let mut sig = InferredSignatureCcJson {
            function_name: "main".to_string(),
            signature: "int32_t main(void)".to_string(),
            ret_type: "int32_t".to_string(),
            params: vec![InferredParamJson {
                name: "arg1".to_string(),
                param_type: "void *".to_string(),
            }],
            callconv: String::new(),
            arch: "aarch64".to_string(),
            confidence: 80,
            callconv_confidence: 0,
        };
        let mut merged = Some(r2types::FunctionSignatureSpec {
            ret_type: Some(r2types::CTypeLike::Int {
                bits: 32,
                signedness: r2types::Signedness::Signed,
            }),
            params: vec![
                r2types::FunctionParamSpec {
                    name: "argc".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Void,
                    ))),
                },
                r2types::FunctionParamSpec {
                    name: "argv".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Void,
                    ))),
                },
                r2types::FunctionParamSpec {
                    name: "envp".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Void,
                    ))),
                },
                r2types::FunctionParamSpec {
                    name: "arg_550h".to_string(),
                    ty: Some(r2types::CTypeLike::Int {
                        bits: 64,
                        signedness: r2types::Signedness::Signed,
                    }),
                },
            ],
        });

        apply_main_signature_override("sym._main", &mut sig, &mut merged);

        assert_eq!(
            sig.params
                .iter()
                .map(|param| (param.name.as_str(), param.param_type.as_str()))
                .collect::<Vec<_>>(),
            vec![("argc", "int"), ("argv", "int8_t**"), ("envp", "int8_t**"),]
        );
        let merged = merged.expect("main signature");
        assert_eq!(merged.params.len(), 3);
        assert_eq!(merged.params[0].name, "argc");
        assert_eq!(merged.params[1].name, "argv");
        assert_eq!(merged.params[2].name, "envp");
    }

    #[test]
    fn merge_register_type_hints_prefers_pointer_over_integer_aliases() {
        let mut metadata = std::collections::HashMap::new();
        merge_type_hint(
            &mut metadata,
            "edi".to_string(),
            TypeHint {
                rank: TypeHintRank::Integer,
                ty: "int32_t".to_string(),
            },
        );
        let mut usage = std::collections::HashMap::new();
        merge_type_hint(&mut usage, "rdi".to_string(), TypeHint::pointer());

        let merged = merge_register_type_hints(&metadata, &usage, X86_ARG_REGS);
        assert_eq!(
            merged.get("rdi").map(|hint| hint.ty.as_str()),
            Some("void *")
        );
        assert_eq!(
            merged.get("edi").map(|hint| hint.ty.as_str()),
            Some("void *")
        );
    }

    #[test]
    fn add_stack_var_upgrades_existing_slot_to_pointer_when_confident() {
        let mut vars = Vec::new();
        let mut seen_slots = std::collections::HashMap::new();
        add_stack_var(
            &mut vars,
            &mut seen_slots,
            "rbp",
            X86_FRAME_BASES,
            -8,
            8,
            None,
        );
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].var_type, "int64_t");

        add_stack_var(
            &mut vars,
            &mut seen_slots,
            "rbp",
            X86_FRAME_BASES,
            -8,
            8,
            Some("void *".to_string()),
        );
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].var_type, "void *");
    }

    #[test]
    fn add_stack_var_keeps_bp_and_sp_slots_distinct_at_same_offset() {
        let mut vars = Vec::new();
        let mut seen_slots = std::collections::HashMap::new();

        add_stack_var(
            &mut vars,
            &mut seen_slots,
            "rsp",
            X86_FRAME_BASES,
            -8,
            8,
            Some("void *".to_string()),
        );
        add_stack_var(
            &mut vars,
            &mut seen_slots,
            "rbp",
            X86_FRAME_BASES,
            -8,
            8,
            None,
        );

        assert_eq!(vars.len(), 2);
        assert!(
            vars.iter()
                .any(|var| var.kind == "s" && var.delta == -8 && var.var_type == "void *")
        );
        assert!(
            vars.iter()
                .any(|var| var.kind == "b" && var.delta == -8 && var.var_type == "int64_t")
        );
    }

    #[test]
    fn scalar_only_argument_evidence_prefers_integer_type() {
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::IntAnd {
                    dst: r2ssa::SSAVar::new("tmp:masked", 1, 4),
                    a: r2ssa::SSAVar::new("esi", 0, 4),
                    b: r2ssa::SSAVar::new("const:ff", 0, 4),
                },
                r2ssa::SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("tmp:eq", 1, 1),
                    a: r2ssa::SSAVar::new("tmp:masked", 1, 4),
                    b: r2ssa::SSAVar::new("const:0", 0, 4),
                },
            ],
        }];
        let evidence_ctx = collect_signature_type_evidence_context(&blocks);
        let initial_ty = r2types::CTypeLike::Unknown;
        let evidence = collect_type_evidence_for_var(
            &evidence_ctx,
            &r2ssa::SSAVar::new("esi", 0, 4),
            &initial_ty,
        );
        let ty = resolve_evidence_driven_type(initial_ty, 4, 64, &evidence);
        assert_eq!(ty, signed_type(32));
    }

    #[test]
    fn deref_argument_evidence_prefers_pointer_type() {
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1100,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:val", 1, 4),
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("rdi", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("eax", 1, 4),
                    a: r2ssa::SSAVar::new("tmp:val", 1, 4),
                    b: r2ssa::SSAVar::new("const:1", 0, 4),
                },
            ],
        }];
        let evidence_ctx = collect_signature_type_evidence_context(&blocks);
        let initial_ty = r2types::CTypeLike::Unknown;
        let evidence = collect_type_evidence_for_var(
            &evidence_ctx,
            &r2ssa::SSAVar::new("rdi", 0, 8),
            &initial_ty,
        );
        let ty = resolve_evidence_driven_type(initial_ty, 8, 64, &evidence);
        assert_eq!(ty, void_ptr_type());
    }

    #[test]
    fn mixed_pointer_and_scalar_evidence_stays_conservative() {
        let evidence = TypeEvidence {
            pointer_proven: 1,
            scalar_likely: 1,
            ..TypeEvidence::default()
        };
        let ty = resolve_evidence_driven_type(r2types::CTypeLike::Unknown, 8, 64, &evidence);
        assert_eq!(ty, void_ptr_type());
    }

    #[test]
    fn bool_like_branch_only_argument_prefers_bool() {
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1200,
            size: 4,
            ops: vec![r2ssa::SSAOp::CBranch {
                target: r2ssa::SSAVar::new("const:1300", 0, 8),
                cond: r2ssa::SSAVar::new("dil", 0, 1),
            }],
        }];
        let evidence_ctx = collect_signature_type_evidence_context(&blocks);
        let initial_ty = r2types::CTypeLike::Unknown;
        let evidence = collect_type_evidence_for_var(
            &evidence_ctx,
            &r2ssa::SSAVar::new("dil", 0, 1),
            &initial_ty,
        );
        let ty = resolve_evidence_driven_type(initial_ty, 1, 64, &evidence);
        assert_eq!(ty, r2types::CTypeLike::Bool);
    }

    #[test]
    fn return_type_evidence_prefers_scalar_for_arithmetic_result() {
        let mut block = r2il::R2ILBlock::new(0x1300, 4);
        block.push(r2il::R2ILOp::IntAdd {
            dst: r2il::Varnode::unique(0x10, 4),
            a: r2il::Varnode::unique(0x20, 4),
            b: r2il::Varnode::constant(1, 4),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::unique(0x10, 4),
        });
        let func = r2ssa::SSAFunction::from_blocks_with_arch(&[block], None).expect("ssa function");
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1300,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:10", 1, 4),
                    a: r2ssa::SSAVar::new("tmp:20", 0, 4),
                    b: r2ssa::SSAVar::new("const:1", 0, 4),
                },
                r2ssa::SSAOp::Return {
                    target: r2ssa::SSAVar::new("tmp:10", 1, 4),
                },
            ],
        }];
        let evidence_ctx = collect_signature_type_evidence_context(&blocks);
        let mut type_inference = r2types::TypeInference::new(64);
        type_inference.infer_function(&func);
        let (ret_ty, _) = infer_signature_return_type(&func, &type_inference, 64, &evidence_ctx);
        assert_eq!(
            ret_ty,
            r2types::CTypeLike::Int {
                bits: 32,
                signedness: r2types::Signedness::Unknown,
            }
        );
    }
}
