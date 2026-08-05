use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use r2ssa::{SSABlock, SSAOp, SSAVar, SSAVarNameKind};

use crate::facts::parse_type_like_spec;
use crate::signature_infer::RecoveredSignatureParam;
use crate::writeback::RecoveredVariable;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SignatureTypeEvidenceContext {
    pub pointer_vars: HashSet<String>,
    pub pointer_pointee_width_bytes: HashMap<String, u32>,
    pub scalar_proven_vars: HashSet<String>,
    pub scalar_likely_vars: HashSet<String>,
    pub bool_like_vars: HashSet<String>,
    pub width_bits: HashMap<String, u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeHintRank {
    Integer = 1,
    Float = 2,
    Pointer = 3,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeHint {
    pub rank: TypeHintRank,
    pub ty: String,
}

struct StackVarRecoveryHint {
    type_override: Option<String>,
    stack_arg_index: Option<usize>,
}

impl TypeHint {
    pub fn pointer() -> Self {
        Self {
            rank: TypeHintRank::Pointer,
            ty: "void *".to_string(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MetadataScalarKind {
    Bool,
    SignedInt,
    UnsignedInt,
    Float,
    Bitvector,
    Unknown,
}

pub fn size_to_signed_int_type(size: u32) -> String {
    match size {
        1 => "int8_t".to_string(),
        2 => "int16_t".to_string(),
        4 => "int32_t".to_string(),
        8 => "int64_t".to_string(),
        _ => format!("int{}_t", size.saturating_mul(8)),
    }
}

pub fn size_to_unsigned_int_type(size: u32) -> String {
    match size {
        1 => "uint8_t".to_string(),
        2 => "uint16_t".to_string(),
        4 => "uint32_t".to_string(),
        8 => "uint64_t".to_string(),
        _ => format!("uint{}_t", size.saturating_mul(8)),
    }
}

pub fn scalar_metadata_type_hint(kind: MetadataScalarKind, size: u32) -> Option<TypeHint> {
    match kind {
        MetadataScalarKind::Bool => Some(TypeHint {
            rank: TypeHintRank::Integer,
            ty: "bool".to_string(),
        }),
        MetadataScalarKind::SignedInt => Some(TypeHint {
            rank: TypeHintRank::Integer,
            ty: size_to_signed_int_type(size),
        }),
        MetadataScalarKind::UnsignedInt => Some(TypeHint {
            rank: TypeHintRank::Integer,
            ty: size_to_unsigned_int_type(size),
        }),
        MetadataScalarKind::Float => {
            let ty = match size {
                4 => "float".to_string(),
                8 => "double".to_string(),
                16 => "long double".to_string(),
                _ => "float".to_string(),
            };
            Some(TypeHint {
                rank: TypeHintRank::Float,
                ty,
            })
        }
        MetadataScalarKind::Bitvector | MetadataScalarKind::Unknown => None,
    }
}

pub fn type_hint_from_value_metadata(
    pointer_like: bool,
    scalar_kind: Option<MetadataScalarKind>,
    size: u32,
) -> Option<TypeHint> {
    if pointer_like {
        return Some(TypeHint::pointer());
    }

    scalar_metadata_type_hint(scalar_kind?, size)
}

pub type ArgAliasMap = &'static [(&'static str, &'static [&'static str])];
pub type BaseRegList = &'static [&'static str];

pub const X86_ARG_REGS: &[(&str, &[&str])] = &[
    ("rdi", &["rdi", "edi", "di", "dil"]),
    ("rsi", &["rsi", "esi", "si", "sil"]),
    ("rdx", &["rdx", "edx", "dx", "dl", "dh"]),
    ("rcx", &["rcx", "ecx", "cx", "cl", "ch"]),
    ("r8", &["r8", "r8d", "r8w", "r8b"]),
    ("r9", &["r9", "r9d", "r9w", "r9b"]),
];
const RISCV_ARG_REGS: &[(&str, &[&str])] = &[
    ("a0", &["a0", "x10"]),
    ("a1", &["a1", "x11"]),
    ("a2", &["a2", "x12"]),
    ("a3", &["a3", "x13"]),
    ("a4", &["a4", "x14"]),
    ("a5", &["a5", "x15"]),
    ("a6", &["a6", "x16"]),
    ("a7", &["a7", "x17"]),
];
const ARM64_ARG_REGS: &[(&str, &[&str])] = &[
    ("x0", &["x0", "w0"]),
    ("x1", &["x1", "w1"]),
    ("x2", &["x2", "w2"]),
    ("x3", &["x3", "w3"]),
    ("x4", &["x4", "w4"]),
    ("x5", &["x5", "w5"]),
    ("x6", &["x6", "w6"]),
    ("x7", &["x7", "w7"]),
];
const ARM32_ARG_REGS: &[(&str, &[&str])] = &[
    ("r0", &["r0"]),
    ("r1", &["r1"]),
    ("r2", &["r2"]),
    ("r3", &["r3"]),
];
const MIPS_ARG_REGS: &[(&str, &[&str])] = &[
    ("a0", &["a0", "$a0", "r4"]),
    ("a1", &["a1", "$a1", "r5"]),
    ("a2", &["a2", "$a2", "r6"]),
    ("a3", &["a3", "$a3", "r7"]),
];
const X86_STACK_BASES: &[&str] = &["rbp", "rsp", "ebp", "esp"];
pub const X86_FRAME_BASES: &[&str] = &["rbp", "ebp"];
const RISCV_STACK_BASES: &[&str] = &["sp", "s0", "fp", "x2", "x8"];
const RISCV_FRAME_BASES: &[&str] = &["s0", "fp", "x8"];
const ARM64_STACK_BASES: &[&str] = &["sp", "x29", "fp"];
const ARM64_FRAME_BASES: &[&str] = &["x29", "fp"];
const ARM32_STACK_BASES: &[&str] = &["sp", "r11", "fp"];
const ARM32_FRAME_BASES: &[&str] = &["r11", "fp"];
const MIPS_STACK_BASES: &[&str] = &["sp", "$sp", "fp", "$fp", "s8", "$s8"];
const MIPS_FRAME_BASES: &[&str] = &["fp", "$fp", "s8", "$s8"];
const GENERIC_STACK_BASES: &[&str] = &["sp", "fp", "bp", "s0", "x2", "x8", "rbp", "rsp"];
const GENERIC_FRAME_BASES: &[&str] = &["fp", "bp", "s0", "x8", "rbp"];

pub fn recover_vars_arch_profile(
    arch_name: Option<&str>,
) -> (ArgAliasMap, BaseRegList, BaseRegList) {
    let Some(arch_name) = arch_name else {
        return (&[], GENERIC_STACK_BASES, GENERIC_FRAME_BASES);
    };

    let arch_name = arch_name.to_ascii_lowercase();
    if arch_name.contains("x86") {
        return (X86_ARG_REGS, X86_STACK_BASES, X86_FRAME_BASES);
    }
    if arch_name.contains("aarch64") || arch_name.contains("arm64") {
        return (ARM64_ARG_REGS, ARM64_STACK_BASES, ARM64_FRAME_BASES);
    }
    if arch_name == "arm" || arch_name.starts_with("armv") {
        return (ARM32_ARG_REGS, ARM32_STACK_BASES, ARM32_FRAME_BASES);
    }
    if arch_name.contains("riscv") || arch_name.starts_with("rv") {
        return (RISCV_ARG_REGS, RISCV_STACK_BASES, RISCV_FRAME_BASES);
    }
    if arch_name.contains("mips") {
        return (MIPS_ARG_REGS, MIPS_STACK_BASES, MIPS_FRAME_BASES);
    }

    (&[], GENERIC_STACK_BASES, GENERIC_FRAME_BASES)
}

fn arch_is_x86_64_sysv_like(arch_name: Option<&str>) -> bool {
    let Some(arch_name) = arch_name else {
        return false;
    };
    let arch_name = arch_name.to_ascii_lowercase();
    arch_name.contains("x86-64")
        || arch_name.contains("x86_64")
        || arch_name.contains("amd64")
        || (arch_name.contains("x86") && arch_name.contains("64"))
}

fn incoming_stack_arg_index(
    arch_name: Option<&str>,
    base: &SSAVar,
    offset: i64,
    ptr_bits: u32,
    arg_reg_count: usize,
) -> Option<usize> {
    if !arch_is_x86_64_sysv_like(arch_name)
        || base.version != 0
        || !base.name.eq_ignore_ascii_case("rsp")
        || ptr_bits != 64
    {
        return None;
    }
    let ptr_bytes = i64::from(ptr_bits / 8);
    if offset < ptr_bytes || (offset - ptr_bytes) % ptr_bytes != 0 {
        return None;
    }
    Some(arg_reg_count + ((offset - ptr_bytes) / ptr_bytes) as usize)
}

fn stack_addr_temp(op: &SSAOp, stack_bases: BaseRegList) -> Option<(&SSAVar, &SSAVar, i64)> {
    match op {
        SSAOp::IntAdd { dst, a, b } => {
            if stack_bases.contains(&a.name.to_ascii_lowercase().as_str())
                && let Some(offset) = parse_const_value(&b.name)
            {
                return Some((dst, a, offset as i64));
            }
            if stack_bases.contains(&b.name.to_ascii_lowercase().as_str())
                && let Some(offset) = parse_const_value(&a.name)
            {
                return Some((dst, b, offset as i64));
            }
            None
        }
        SSAOp::IntSub { dst, a, b } => {
            if stack_bases.contains(&a.name.to_ascii_lowercase().as_str())
                && let Some(offset) = parse_const_value(&b.name)
            {
                return Some((dst, a, -(offset as i64)));
            }
            None
        }
        _ => None,
    }
}

fn incoming_stack_arg_addr_temp<'a>(
    op: &'a SSAOp,
    arch_name: Option<&str>,
    ptr_bits: u32,
    arg_reg_count: usize,
) -> Option<(&'a SSAVar, &'a SSAVar, i64)> {
    let (dst, base, offset) = stack_addr_temp(op, &["rsp"])?;
    if incoming_stack_arg_index(arch_name, base, offset, ptr_bits, arg_reg_count).is_some() {
        Some((dst, base, offset))
    } else {
        None
    }
}

pub fn size_to_type(size: u32) -> String {
    match size {
        1 => "int8_t".to_string(),
        2 => "int16_t".to_string(),
        4 => "int32_t".to_string(),
        8 => "int64_t".to_string(),
        _ => format!("byte[{size}]"),
    }
}

pub fn ssa_var_key(var: &SSAVar) -> String {
    format!("{}_{}", var.name.to_ascii_lowercase(), var.version)
}

pub fn ssa_var_block_key(block_addr: u64, var: &SSAVar) -> String {
    format!("{}@{block_addr:x}", ssa_var_key(var))
}

pub fn scalar_register_family_key(name: &str) -> String {
    let lower = name.to_ascii_lowercase();

    if let Some(idx) = lower.strip_prefix('x').or_else(|| lower.strip_prefix('w'))
        && !idx.is_empty()
        && idx.chars().all(|ch| ch.is_ascii_digit())
    {
        return format!("aarch64:gpr:{idx}");
    }

    match lower.as_str() {
        "fp" => "aarch64:gpr:29".to_string(),
        "lr" => "aarch64:gpr:30".to_string(),
        "sp" | "wsp" => "aarch64:sp".to_string(),
        "xzr" | "wzr" => "aarch64:zr".to_string(),
        _ => lower,
    }
}

pub fn merge_type_hint(hints: &mut HashMap<String, TypeHint>, key: String, incoming: TypeHint) {
    match hints.get(&key) {
        Some(current) if !incoming_hint_should_replace(current, &incoming) => {}
        _ => {
            hints.insert(key, incoming);
        }
    }
}

pub fn collect_signature_type_evidence_context(
    ssa_blocks: &[SSABlock],
) -> SignatureTypeEvidenceContext {
    let pointer_vars = infer_pointer_var_keys_from_ssa(ssa_blocks);
    let pointer_pointee_width_bytes = infer_pointer_pointee_width_bytes(ssa_blocks, &pointer_vars);
    let (scalar_proven_vars, scalar_likely_vars, bool_like_vars, mut width_bits) =
        infer_scalar_var_evidence_from_ssa(ssa_blocks);
    let register_versions = collect_register_version_keys(ssa_blocks);
    normalize_register_family_width_hints(&register_versions, &mut width_bits);
    propagate_normalized_scalar_result_widths(ssa_blocks, &mut width_bits);
    normalize_register_family_width_hints(&register_versions, &mut width_bits);
    SignatureTypeEvidenceContext {
        pointer_vars,
        pointer_pointee_width_bytes,
        scalar_proven_vars,
        scalar_likely_vars,
        bool_like_vars,
        width_bits,
    }
}

pub fn collect_pointer_arg_slots(vars: &[RecoveredVariable]) -> BTreeSet<usize> {
    vars.iter()
        .filter(|var| var.kind == "r" && var.isarg && var.var_type.contains('*'))
        .filter_map(|var| {
            var.name
                .strip_prefix("arg")
                .and_then(|idx| idx.parse::<usize>().ok())
        })
        .collect()
}

pub fn recover_signature_params_from_ssa(
    ssa_blocks: &[SSABlock],
    arch_name: Option<&str>,
    metadata_reg_type_hints: &HashMap<String, TypeHint>,
    semantic_metadata_enabled: bool,
    ptr_bits: u32,
) -> Vec<RecoveredSignatureParam> {
    let (arg_regs, _, _) = recover_vars_arch_profile(arch_name);
    if arg_regs.is_empty() {
        return Vec::new();
    }

    let signature_evidence = collect_signature_type_evidence_context(ssa_blocks);
    let (usage_reg_type_hints, _pointer_var_keys) = infer_usage_register_type_hints(ssa_blocks);
    let empty_metadata_hints = HashMap::new();
    let enabled_metadata_hints = if semantic_metadata_enabled {
        metadata_reg_type_hints
    } else {
        &empty_metadata_hints
    };
    let reg_type_hints =
        merge_register_type_hints(enabled_metadata_hints, &usage_reg_type_hints, arg_regs);

    let mut seen_arg_regs: HashSet<String> = HashSet::new();
    let mut seen_stack_args: HashSet<usize> = HashSet::new();
    let mut params = Vec::new();
    let mut stack_addr_temps: HashMap<String, (SSAVar, i64)> = HashMap::new();
    let control_return_targets = collect_control_return_targets(ssa_blocks);

    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::IntAdd { .. } | SSAOp::IntSub { .. } => {
                    if let Some((dst, base, offset)) =
                        incoming_stack_arg_addr_temp(op, arch_name, ptr_bits, arg_regs.len())
                    {
                        let dst_key = ssa_var_block_key(block.addr, dst);
                        stack_addr_temps.insert(dst_key, (base.clone(), offset));
                    }
                }
                SSAOp::Load { dst, addr, .. } => {
                    let addr_key = ssa_var_block_key(block.addr, addr);
                    if !control_return_targets.contains(&ssa_var_key(dst))
                        && let Some((base, offset)) = stack_addr_temps.get(&addr_key)
                        && let Some(index) = incoming_stack_arg_index(
                            arch_name,
                            base,
                            *offset,
                            ptr_bits,
                            arg_regs.len(),
                        )
                        && seen_stack_args.insert(index)
                    {
                        let hinted_type =
                            if signature_evidence.pointer_vars.contains(&ssa_var_key(dst)) {
                                Some("void *")
                            } else {
                                None
                            };
                        let initial_ty = hinted_type
                            .and_then(|ty| parse_type_like_spec(ty, ptr_bits))
                            .unwrap_or_else(|| size_to_type_like(dst.size));
                        params.push(RecoveredSignatureParam {
                            name: format!("arg{index}"),
                            ssa_var: dst.clone(),
                            initial_ty,
                        });
                    }
                }
                _ => {}
            }

            for src in op.sources() {
                if src.version != 0 {
                    continue;
                }
                let base_name = src.name.to_lowercase();
                for (index, (canonical, aliases)) in arg_regs.iter().enumerate() {
                    if !aliases.contains(&base_name.as_str()) || seen_arg_regs.contains(*canonical)
                    {
                        continue;
                    }
                    seen_arg_regs.insert(canonical.to_string());
                    let hinted_type = recovered_arg_type_hint(
                        &reg_type_hints,
                        canonical,
                        aliases,
                        src,
                        Some(&signature_evidence),
                        ptr_bits,
                    );
                    let initial_ty = hinted_type
                        .as_deref()
                        .and_then(|ty| parse_type_like_spec(ty, ptr_bits))
                        .unwrap_or_else(|| size_to_type_like(src.size));
                    params.push(RecoveredSignatureParam {
                        name: format!("arg{index}"),
                        ssa_var: src.clone(),
                        initial_ty,
                    });
                    break;
                }
            }
        }
    }

    params
}

pub fn recover_vars_from_ssa(
    ssa_blocks: &[SSABlock],
    arch_name: Option<&str>,
    metadata_reg_type_hints: &HashMap<String, TypeHint>,
    semantic_metadata_enabled: bool,
) -> Vec<RecoveredVariable> {
    let mut vars = Vec::new();
    let mut seen_slots: HashMap<(bool, i64), usize> = HashMap::new();
    let mut seen_arg_regs: HashSet<String> = HashSet::new();
    let (arg_regs, stack_bases, frame_bases) = recover_vars_arch_profile(arch_name);
    let ptr_bits = if arch_is_x86_64_sysv_like(arch_name) {
        64
    } else {
        0
    };
    let signature_evidence = collect_signature_type_evidence_context(ssa_blocks);
    let (usage_reg_type_hints, pointer_var_keys) = infer_usage_register_type_hints(ssa_blocks);
    let empty_metadata_hints = HashMap::new();
    let enabled_metadata_hints = if semantic_metadata_enabled {
        metadata_reg_type_hints
    } else {
        &empty_metadata_hints
    };
    let reg_type_hints =
        merge_register_type_hints(enabled_metadata_hints, &usage_reg_type_hints, arg_regs);

    let mut stack_addr_temps: HashMap<String, (SSAVar, i64)> = HashMap::new();
    let control_return_targets = collect_control_return_targets(ssa_blocks);

    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::IntAdd { dst, .. } | SSAOp::IntSub { dst, .. } => {
                    if let Some((_, base, offset)) = stack_addr_temp(op, stack_bases) {
                        let dst_key = ssa_var_block_key(block.addr, dst);
                        stack_addr_temps.insert(dst_key, (base.clone(), offset));
                    }
                }
                SSAOp::Store { addr, val, .. } => {
                    let addr_key = ssa_var_block_key(block.addr, addr);
                    if let Some((base, offset)) = stack_addr_temps.get(&addr_key) {
                        let type_override = if pointer_var_keys.contains(&ssa_var_key(val)) {
                            Some("void *".to_string())
                        } else {
                            None
                        };
                        add_stack_var(
                            &mut vars,
                            &mut seen_slots,
                            &base.name.to_ascii_lowercase(),
                            frame_bases,
                            *offset,
                            val.size,
                            StackVarRecoveryHint {
                                type_override,
                                stack_arg_index: incoming_stack_arg_index(
                                    arch_name,
                                    base,
                                    *offset,
                                    ptr_bits,
                                    arg_regs.len(),
                                ),
                            },
                        );
                    }
                }
                SSAOp::Load { dst, addr, .. } => {
                    let addr_key = ssa_var_block_key(block.addr, addr);
                    if !control_return_targets.contains(&ssa_var_key(dst))
                        && let Some((base, offset)) = stack_addr_temps.get(&addr_key)
                    {
                        let type_override = if pointer_var_keys.contains(&ssa_var_key(dst)) {
                            Some("void *".to_string())
                        } else {
                            None
                        };
                        add_stack_var(
                            &mut vars,
                            &mut seen_slots,
                            &base.name.to_ascii_lowercase(),
                            frame_bases,
                            *offset,
                            dst.size,
                            StackVarRecoveryHint {
                                type_override,
                                stack_arg_index: incoming_stack_arg_index(
                                    arch_name,
                                    base,
                                    *offset,
                                    ptr_bits,
                                    arg_regs.len(),
                                ),
                            },
                        );
                    }
                }
                _ => {}
            }

            for src in op.sources() {
                let base_name = src.name.to_lowercase();
                if src.version == 0 {
                    for (i, (canonical, aliases)) in arg_regs.iter().enumerate() {
                        if aliases.contains(&base_name.as_str())
                            && !seen_arg_regs.contains(*canonical)
                        {
                            seen_arg_regs.insert(canonical.to_string());
                            let hinted_type = recovered_arg_type_hint(
                                &reg_type_hints,
                                canonical,
                                aliases,
                                src,
                                Some(&signature_evidence),
                                ptr_bits,
                            );
                            vars.push(RecoveredVariable {
                                name: format!("arg{i}"),
                                kind: "r".to_string(),
                                delta: 0,
                                var_type: hinted_type.unwrap_or_else(|| size_to_type(src.size)),
                                isarg: true,
                                reg: Some(canonical.to_string()),
                            });
                            break;
                        }
                    }
                }
            }
        }
    }

    vars.sort_by_key(|v| v.delta);
    vars
}

fn collect_control_return_targets(ssa_blocks: &[SSABlock]) -> HashSet<String> {
    ssa_blocks
        .iter()
        .flat_map(|block| &block.ops)
        .filter_map(|op| match op {
            SSAOp::Return { target } => Some(ssa_var_key(target)),
            _ => None,
        })
        .collect()
}

fn size_to_type_like(size: u32) -> crate::CTypeLike {
    let bits = match size {
        1 => 8,
        2 => 16,
        4 => 32,
        8 => 64,
        _ => return crate::CTypeLike::Unknown,
    };
    crate::CTypeLike::Int {
        bits,
        signedness: crate::Signedness::Signed,
    }
}

fn incoming_hint_should_replace(current: &TypeHint, incoming: &TypeHint) -> bool {
    incoming.rank > current.rank || (incoming.rank == current.rank && incoming.ty < current.ty)
}

fn parse_const_value(name: &str) -> Option<u64> {
    let val_str = name
        .strip_prefix("const:")
        .or_else(|| name.strip_prefix("CONST:"))?;
    let val_str = val_str.split('_').next().unwrap_or(val_str);
    if let Some(hex) = val_str
        .strip_prefix("0x")
        .or_else(|| val_str.strip_prefix("0X"))
    {
        return u64::from_str_radix(hex, 16).ok();
    }
    if let Some(dec) = val_str
        .strip_prefix("0d")
        .or_else(|| val_str.strip_prefix("0D"))
    {
        return dec.parse::<u64>().ok();
    }
    if val_str.chars().all(|c| c.is_ascii_hexdigit()) {
        return u64::from_str_radix(val_str, 16).ok();
    }
    val_str.parse::<u64>().ok()
}

fn ssa_var_is_const(var: &SSAVar) -> bool {
    parse_const_value(&var.name).is_some()
}

pub(crate) fn ssa_var_is_register_like(var: &SSAVar) -> bool {
    let lower = var.name.to_ascii_lowercase();
    matches!(
        SSAVarNameKind::classify(&lower),
        SSAVarNameKind::RegisterAlias | SSAVarNameKind::Ordinary
    )
}

fn strongest_hint_for_aliases(
    hints: &HashMap<String, TypeHint>,
    canonical: &str,
    aliases: &[&str],
) -> Option<TypeHint> {
    let mut best = hints.get(canonical).cloned();
    for alias in aliases {
        if let Some(candidate) = hints.get(*alias).cloned() {
            match &best {
                Some(current) if !incoming_hint_should_replace(current, &candidate) => {}
                _ => best = Some(candidate),
            }
        }
    }
    best
}

fn width_hint_key_matches_family(key: &str, family: &str) -> bool {
    let Some((name, _version)) = key.rsplit_once('_') else {
        return false;
    };
    scalar_register_family_key(name) == family
}

fn width_hint_key_matches_family_version(key: &str, family: &str, version: u32) -> bool {
    let Some((name, version_str)) = key.rsplit_once('_') else {
        return false;
    };
    version_str.parse::<u32>().ok() == Some(version) && scalar_register_family_key(name) == family
}

fn recovered_arg_family_width_hint(
    evidence: &SignatureTypeEvidenceContext,
    src: &SSAVar,
) -> Option<u32> {
    let family = scalar_register_family_key(&src.name);
    evidence
        .width_bits
        .iter()
        .filter(|(key, bits)| {
            **bits > 0 && width_hint_key_matches_family_version(key, &family, src.version)
        })
        .map(|(_, bits)| *bits)
        .min()
        .or_else(|| {
            evidence
                .width_bits
                .iter()
                .filter(|(key, bits)| **bits > 0 && width_hint_key_matches_family(key, &family))
                .map(|(_, bits)| *bits)
                .min()
        })
}

fn recovered_arg_type_hint(
    reg_type_hints: &HashMap<String, TypeHint>,
    canonical: &str,
    aliases: &[&str],
    src: &SSAVar,
    signature_evidence: Option<&SignatureTypeEvidenceContext>,
    ptr_bits: u32,
) -> Option<String> {
    let best_hint = strongest_hint_for_aliases(reg_type_hints, canonical, aliases);
    if let Some(hint) = best_hint.as_ref()
        && hint.rank == TypeHintRank::Pointer
    {
        if let Some(width) = signature_evidence.and_then(|evidence| {
            evidence
                .pointer_pointee_width_bytes
                .get(&ssa_var_key(src))
                .copied()
        }) {
            return Some(format!("{} *", size_to_type(width)));
        }
        return Some(hint.ty.clone());
    }
    let hint = if let Some(evidence) = signature_evidence
        && let Some(bits) = recovered_arg_family_width_hint(evidence, src)
    {
        Some(size_to_type(bits.div_ceil(8)))
    } else {
        best_hint.map(|hint| hint.ty)
    }?;
    match parse_type_like_spec(&hint, ptr_bits) {
        Some(crate::CTypeLike::Int { bits, .. }) if bits > src.size.saturating_mul(8) => {
            Some(size_to_type(src.size))
        }
        _ => Some(hint),
    }
}

fn merge_register_type_hints(
    metadata_hints: &HashMap<String, TypeHint>,
    usage_hints: &HashMap<String, TypeHint>,
    arg_regs: ArgAliasMap,
) -> HashMap<String, TypeHint> {
    let mut merged = HashMap::new();

    for (reg, hint) in metadata_hints {
        merge_type_hint(&mut merged, reg.clone(), hint.clone());
    }
    for (reg, hint) in usage_hints {
        merge_type_hint(&mut merged, reg.clone(), hint.clone());
    }

    for (canonical, aliases) in arg_regs {
        if let Some(best) = strongest_hint_for_aliases(&merged, canonical, aliases) {
            merge_type_hint(&mut merged, (*canonical).to_string(), best.clone());
            for alias in *aliases {
                merge_type_hint(&mut merged, alias.to_string(), best.clone());
            }
        }
    }

    merged
}

fn add_stack_var(
    vars: &mut Vec<RecoveredVariable>,
    seen_slots: &mut HashMap<(bool, i64), usize>,
    base_reg: &str,
    frame_bases: &[&str],
    offset: i64,
    size: u32,
    hint: StackVarRecoveryHint,
) {
    let StackVarRecoveryHint {
        type_override,
        stack_arg_index,
    } = hint;
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

    let is_arg = stack_arg_index.is_some() || if is_frame_base { offset > 0 } else { false };
    let var_name = if let Some(index) = stack_arg_index {
        format!("arg{index}")
    } else if is_arg && offset > 8 {
        format!("arg_{:x}h", offset.unsigned_abs())
    } else {
        format!("var_{:x}h", offset.unsigned_abs())
    };
    let kind = if is_frame_base { "b" } else { "s" };

    vars.push(RecoveredVariable {
        name: var_name,
        kind: kind.to_string(),
        delta: offset,
        var_type: type_override.unwrap_or_else(|| size_to_type(size)),
        isarg: stack_arg_index.is_some() || (is_arg && offset > 8),
        reg: None,
    });
    seen_slots.insert(slot_key, vars.len().saturating_sub(1));
}

fn collect_register_version_keys(ssa_blocks: &[SSABlock]) -> HashMap<String, Vec<String>> {
    let mut reg_versions: HashMap<String, Vec<String>> = HashMap::new();
    for block in ssa_blocks {
        for op in &block.ops {
            let mut collect_var = |var: &SSAVar| {
                if !ssa_var_is_register_like(var) {
                    return;
                }
                let reg_name = scalar_register_family_key(&var.name);
                reg_versions
                    .entry(reg_name)
                    .or_default()
                    .push(ssa_var_key(var));
            };
            if let Some(dst) = op.dst() {
                collect_var(dst);
            }
            op.for_each_source(&mut collect_var);
        }
    }
    for keys in reg_versions.values_mut() {
        keys.sort();
        keys.dedup();
    }
    reg_versions
}

fn set_width_hint_prefer_narrower(
    width_hints: &mut HashMap<String, u32>,
    key: String,
    bits: u32,
) -> bool {
    if bits == 0 {
        return false;
    }
    match width_hints.get(&key).copied() {
        Some(current) if current == bits => false,
        Some(current) if current > 0 && current <= bits => false,
        _ => {
            width_hints.insert(key, bits);
            true
        }
    }
}

fn normalize_register_family_width_hints(
    register_versions: &HashMap<String, Vec<String>>,
    width_hints: &mut HashMap<String, u32>,
) -> bool {
    let mut changed = false;
    for reg_keys in register_versions.values() {
        let max_bits = reg_keys
            .iter()
            .filter_map(|key| width_hints.get(key).copied())
            .max()
            .unwrap_or(0);
        let min_bits = reg_keys
            .iter()
            .filter_map(|key| {
                let current = width_hints.get(key).copied().unwrap_or(0);
                let natural = register_key_natural_bits(key).unwrap_or(0);
                let candidate = match (current, natural) {
                    (0, 0) => 0,
                    (0, natural) => natural,
                    (current, 0) => current,
                    (current, natural) => current.min(natural),
                };
                (candidate > 0).then_some(candidate)
            })
            .min()
            .unwrap_or(0);
        let preferred_bits = if min_bits > 0 && max_bits == 64 && min_bits <= 32 {
            min_bits
        } else {
            max_bits
        };
        for key in reg_keys {
            changed |= set_width_hint_prefer_narrower(width_hints, key.clone(), preferred_bits);
        }
    }
    changed
}

fn register_key_natural_bits(key: &str) -> Option<u32> {
    let reg = key.split('_').next()?;
    if let Some(idx) = reg.strip_prefix('w')
        && !idx.is_empty()
        && idx.chars().all(|ch| ch.is_ascii_digit())
    {
        return Some(32);
    }
    if let Some(idx) = reg.strip_prefix('x')
        && !idx.is_empty()
        && idx.chars().all(|ch| ch.is_ascii_digit())
    {
        return Some(64);
    }
    match reg {
        "wsp" | "wzr" => Some(32),
        "sp" | "fp" | "lr" | "xzr" => Some(64),
        _ => None,
    }
}

fn propagate_normalized_scalar_result_widths(
    ssa_blocks: &[SSABlock],
    width_hints: &mut HashMap<String, u32>,
) -> bool {
    let mut changed = false;
    for block in ssa_blocks {
        for op in &block.ops {
            let (dst, source_bits) = match op {
                SSAOp::Copy { dst, src }
                | SSAOp::Cast { dst, src }
                | SSAOp::New { dst, src }
                | SSAOp::IntZExt { dst, src }
                | SSAOp::IntSExt { dst, src }
                | SSAOp::Subpiece { dst, src, .. } => {
                    let bits = width_hints.get(&ssa_var_key(src)).copied().unwrap_or(0);
                    (dst, bits)
                }
                SSAOp::IntAdd { dst, a, b }
                | SSAOp::IntSub { dst, a, b }
                | SSAOp::IntMult { dst, a, b }
                | SSAOp::IntDiv { dst, a, b }
                | SSAOp::IntSDiv { dst, a, b }
                | SSAOp::IntRem { dst, a, b }
                | SSAOp::IntSRem { dst, a, b }
                | SSAOp::IntAnd { dst, a, b }
                | SSAOp::IntOr { dst, a, b }
                | SSAOp::IntXor { dst, a, b }
                | SSAOp::IntLeft { dst, a, b }
                | SSAOp::IntRight { dst, a, b }
                | SSAOp::IntSRight { dst, a, b } => {
                    let bits = [a, b]
                        .into_iter()
                        .filter(|var| !ssa_var_is_const(var))
                        .filter_map(|var| width_hints.get(&ssa_var_key(var)).copied())
                        .filter(|bits| *bits > 0)
                        .max()
                        .unwrap_or(0);
                    (dst, bits)
                }
                _ => continue,
            };
            changed |= set_width_hint_prefer_narrower(width_hints, ssa_var_key(dst), source_bits);
        }
    }
    changed
}

fn ssa_var_is_stack_base(var: &SSAVar) -> bool {
    matches!(
        var.name.to_ascii_lowercase().as_str(),
        "rbp" | "rsp" | "ebp" | "esp" | "sp" | "fp" | "bp" | "s0" | "x2" | "x8"
    )
}

fn infer_pointer_width_bytes(ssa_blocks: &[SSABlock]) -> u32 {
    let mut width = 0u32;
    for block in ssa_blocks {
        for op in &block.ops {
            if let Some(dst) = op.dst()
                && ssa_var_is_stack_base(dst)
            {
                width = width.max(dst.size);
            }
            op.for_each_source(|src| {
                if ssa_var_is_stack_base(src) {
                    width = width.max(src.size);
                }
            });
        }
    }
    if width == 0 { 8 } else { width }
}

fn infer_index_like_var_keys(ssa_blocks: &[SSABlock]) -> HashSet<String> {
    let mut index_like: HashSet<String> = HashSet::new();
    for block in ssa_blocks {
        for op in &block.ops {
            if let SSAOp::IntSExt { dst, src } | SSAOp::IntZExt { dst, src } = op
                && src.size < dst.size
            {
                index_like.insert(ssa_var_key(dst));
            }
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for block in ssa_blocks {
            for op in &block.ops {
                match op {
                    SSAOp::Copy { dst, src }
                    | SSAOp::Cast { dst, src }
                    | SSAOp::New { dst, src } => {
                        if index_like.contains(&ssa_var_key(src)) {
                            changed |= index_like.insert(ssa_var_key(dst));
                        }
                    }
                    SSAOp::IntMult { dst, a, b } => {
                        let a_key = ssa_var_key(a);
                        let b_key = ssa_var_key(b);
                        let a_is_scaled_const = ssa_var_is_const(a);
                        let b_is_scaled_const = ssa_var_is_const(b);
                        if (index_like.contains(&a_key) && ssa_var_is_const(b))
                            || (index_like.contains(&b_key) && ssa_var_is_const(a))
                            || (a_is_scaled_const && !b_is_scaled_const)
                            || (b_is_scaled_const && !a_is_scaled_const)
                        {
                            changed |= index_like.insert(ssa_var_key(dst));
                        }
                    }
                    SSAOp::IntLeft { dst, a, b } => {
                        let shift_amount = parse_const_value(&b.name).unwrap_or(u64::MAX);
                        if (index_like.contains(&ssa_var_key(a)) && ssa_var_is_const(b))
                            || shift_amount <= 6
                        {
                            changed |= index_like.insert(ssa_var_key(dst));
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    index_like
}

fn infer_pointer_var_keys_from_ssa(ssa_blocks: &[SSABlock]) -> HashSet<String> {
    let mut pointer_vars: HashSet<String> = HashSet::new();
    let register_versions = collect_register_version_keys(ssa_blocks);
    let index_like_vars = infer_index_like_var_keys(ssa_blocks);
    let pointer_width = infer_pointer_width_bytes(ssa_blocks);
    let mut stack_addr_slots: HashMap<String, String> = HashMap::new();
    let mut pointer_stack_slots: HashSet<String> = HashSet::new();

    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::IntAdd { dst, a, b } | SSAOp::IntSub { dst, a, b } => {
                    let a_is_stack = ssa_var_is_stack_base(a);
                    let b_is_stack = ssa_var_is_stack_base(b);
                    let a_const = parse_const_value(&a.name);
                    let b_const = parse_const_value(&b.name);

                    if a_is_stack && b_const.is_some() {
                        let raw = b_const.unwrap_or(0);
                        let offset = if matches!(op, SSAOp::IntSub { .. }) {
                            -(raw as i64)
                        } else {
                            raw as i64
                        };
                        stack_addr_slots.insert(
                            ssa_var_block_key(block.addr, dst),
                            format!("{}:{offset}", a.name.to_ascii_lowercase()),
                        );
                    } else if matches!(op, SSAOp::IntAdd { .. }) && b_is_stack && a_const.is_some()
                    {
                        let raw = a_const.unwrap_or(0);
                        stack_addr_slots.insert(
                            ssa_var_block_key(block.addr, dst),
                            format!("{}:{}", b.name.to_ascii_lowercase(), raw as i64),
                        );
                    }
                }
                SSAOp::Load { addr, .. }
                | SSAOp::Store { addr, .. }
                | SSAOp::LoadLinked { addr, .. }
                | SSAOp::StoreConditional { addr, .. }
                | SSAOp::LoadGuarded { addr, .. }
                | SSAOp::StoreGuarded { addr, .. }
                | SSAOp::AtomicCAS { addr, .. } => {
                    pointer_vars.insert(ssa_var_key(addr));
                }
                _ => {}
            }
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for block in ssa_blocks {
            for op in &block.ops {
                match op {
                    SSAOp::Phi { dst, sources } => {
                        let dst_key = ssa_var_key(dst);
                        let dst_is_pointer = pointer_vars.contains(&dst_key);
                        let any_source_pointer = sources
                            .iter()
                            .any(|src| pointer_vars.contains(&ssa_var_key(src)));

                        if any_source_pointer {
                            changed |= pointer_vars.insert(dst_key.clone());
                        }
                        if dst_is_pointer {
                            for src in sources {
                                changed |= pointer_vars.insert(ssa_var_key(src));
                            }
                        }
                    }
                    SSAOp::Copy { dst, src }
                    | SSAOp::Cast { dst, src }
                    | SSAOp::New { dst, src } => {
                        let dst_key = ssa_var_key(dst);
                        let src_key = ssa_var_key(src);
                        if pointer_vars.contains(&dst_key) {
                            changed |= pointer_vars.insert(src_key.clone());
                        }
                        if pointer_vars.contains(&src_key) {
                            changed |= pointer_vars.insert(dst_key);
                        }
                    }
                    SSAOp::IntAdd { dst, a, b } | SSAOp::IntSub { dst, a, b } => {
                        let dst_key = ssa_var_key(dst);
                        let a_key = ssa_var_key(a);
                        let b_key = ssa_var_key(b);
                        let a_is_const = ssa_var_is_const(a);
                        let b_is_const = ssa_var_is_const(b);
                        let a_index_like = index_like_vars.contains(&a_key);
                        let b_index_like = index_like_vars.contains(&b_key);

                        if pointer_vars.contains(&dst_key) {
                            if a_is_const && !b_is_const {
                                changed |= pointer_vars.insert(b_key.clone());
                            } else if b_is_const && !a_is_const {
                                changed |= pointer_vars.insert(a_key.clone());
                            } else if a_index_like && !b_index_like {
                                changed |= pointer_vars.insert(b_key.clone());
                            } else if b_index_like && !a_index_like {
                                changed |= pointer_vars.insert(a_key.clone());
                            } else if a_index_like && b_index_like {
                                let a_is_tmp = a.is_temp();
                                let b_is_tmp = b.is_temp();
                                if a_is_tmp && !b_is_tmp {
                                    changed |= pointer_vars.insert(b_key.clone());
                                } else if b_is_tmp && !a_is_tmp {
                                    changed |= pointer_vars.insert(a_key.clone());
                                }
                            }
                        }

                        if pointer_vars.contains(&a_key) && b_is_const {
                            changed |= pointer_vars.insert(dst_key.clone());
                        }
                        if pointer_vars.contains(&b_key) && a_is_const {
                            changed |= pointer_vars.insert(dst_key.clone());
                        }
                        if pointer_vars.contains(&a_key) && index_like_vars.contains(&b_key) {
                            changed |= pointer_vars.insert(dst_key.clone());
                        }
                        if pointer_vars.contains(&b_key) && index_like_vars.contains(&a_key) {
                            changed |= pointer_vars.insert(dst_key.clone());
                        }
                    }
                    SSAOp::PtrAdd { dst, base, .. } | SSAOp::PtrSub { dst, base, .. } => {
                        let dst_key = ssa_var_key(dst);
                        let base_key = ssa_var_key(base);
                        if pointer_vars.contains(&dst_key) {
                            changed |= pointer_vars.insert(base_key.clone());
                        }
                        if pointer_vars.contains(&base_key) {
                            changed |= pointer_vars.insert(dst_key);
                        }
                    }
                    SSAOp::SegmentOp { dst, offset, .. } => {
                        let dst_key = ssa_var_key(dst);
                        let offset_key = ssa_var_key(offset);
                        if pointer_vars.contains(&dst_key) {
                            changed |= pointer_vars.insert(offset_key.clone());
                        }
                        if pointer_vars.contains(&offset_key) {
                            changed |= pointer_vars.insert(dst_key);
                        }
                    }
                    SSAOp::Store { addr, val, .. } => {
                        if let Some(slot) =
                            stack_addr_slots.get(&ssa_var_block_key(block.addr, addr))
                        {
                            let val_key = ssa_var_key(val);
                            if val.size >= pointer_width && pointer_vars.contains(&val_key) {
                                changed |= pointer_stack_slots.insert(slot.clone());
                            }
                            if val.size >= pointer_width && pointer_stack_slots.contains(slot) {
                                changed |= pointer_vars.insert(val_key);
                            }
                        }
                    }
                    SSAOp::Load { dst, addr, .. } => {
                        if let Some(slot) =
                            stack_addr_slots.get(&ssa_var_block_key(block.addr, addr))
                        {
                            let dst_key = ssa_var_key(dst);
                            if dst.size >= pointer_width && pointer_stack_slots.contains(slot) {
                                changed |= pointer_vars.insert(dst_key.clone());
                            }
                            if dst.size >= pointer_width && pointer_vars.contains(&dst_key) {
                                changed |= pointer_stack_slots.insert(slot.clone());
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        for reg_keys in register_versions.values() {
            if reg_keys.iter().any(|key| pointer_vars.contains(key)) {
                for key in reg_keys {
                    changed |= pointer_vars.insert(key.clone());
                }
            }
        }
    }

    pointer_vars
}

fn infer_pointer_pointee_width_bytes(
    ssa_blocks: &[SSABlock],
    pointer_vars: &HashSet<String>,
) -> HashMap<String, u32> {
    let mut stack_addr_slots: HashMap<String, String> = HashMap::new();
    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::IntAdd { dst, a, b } => {
                    let (base, offset) = if ssa_var_is_stack_base(a) {
                        (a, parse_const_value(&b.name).map(|value| value as i64))
                    } else if ssa_var_is_stack_base(b) {
                        (b, parse_const_value(&a.name).map(|value| value as i64))
                    } else {
                        continue;
                    };
                    if let Some(offset) = offset {
                        stack_addr_slots.insert(
                            ssa_var_block_key(block.addr, dst),
                            format!("{}:{offset}", base.name.to_ascii_lowercase()),
                        );
                    }
                }
                SSAOp::IntSub { dst, a, b } if ssa_var_is_stack_base(a) => {
                    if let Some(offset) = parse_const_value(&b.name) {
                        stack_addr_slots.insert(
                            ssa_var_block_key(block.addr, dst),
                            format!("{}:{}", a.name.to_ascii_lowercase(), -(offset as i64)),
                        );
                    }
                }
                _ => {}
            }
        }
    }

    let mut adjacency: HashMap<String, HashSet<String>> = HashMap::new();
    let mut stack_pointer_values: HashMap<String, Vec<String>> = HashMap::new();
    let mut widths: HashMap<String, BTreeSet<u32>> = HashMap::new();

    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::Copy { dst, src } | SSAOp::Cast { dst, src } | SSAOp::New { dst, src } => {
                    add_pointer_pointee_flow_edge(&mut adjacency, pointer_vars, dst, src)
                }
                SSAOp::Phi { dst, sources } => {
                    for src in sources {
                        add_pointer_pointee_flow_edge(&mut adjacency, pointer_vars, dst, src);
                    }
                }
                SSAOp::IntAdd { dst, a, b } | SSAOp::IntSub { dst, a, b } => {
                    let b_is_nonzero_const =
                        parse_const_value(&b.name).is_some_and(|value| value != 0);
                    if !ssa_var_is_stack_base(a) && !b_is_nonzero_const {
                        add_pointer_pointee_flow_edge(&mut adjacency, pointer_vars, dst, a);
                    }
                    let a_is_nonzero_const =
                        parse_const_value(&a.name).is_some_and(|value| value != 0);
                    if !ssa_var_is_stack_base(b)
                        && !a_is_nonzero_const
                        && !matches!(op, SSAOp::IntSub { .. })
                    {
                        add_pointer_pointee_flow_edge(&mut adjacency, pointer_vars, dst, b);
                    }
                }
                SSAOp::PtrAdd { dst, base, .. } | SSAOp::PtrSub { dst, base, .. } => {
                    add_pointer_pointee_flow_edge(&mut adjacency, pointer_vars, dst, base);
                }
                SSAOp::SegmentOp { dst, offset, .. } => {
                    add_pointer_pointee_flow_edge(&mut adjacency, pointer_vars, dst, offset)
                }
                SSAOp::Load { dst, addr, .. } => {
                    let addr_key = ssa_var_key(addr);
                    if pointer_vars.contains(&addr_key) {
                        widths.entry(addr_key).or_default().insert(dst.size);
                    }
                    if let Some(slot) = stack_addr_slots.get(&ssa_var_block_key(block.addr, addr)) {
                        let dst_key = ssa_var_key(dst);
                        if pointer_vars.contains(&dst_key) {
                            stack_pointer_values
                                .entry(slot.clone())
                                .or_default()
                                .push(dst_key);
                        }
                    }
                }
                SSAOp::Store { addr, val, .. } => {
                    let addr_key = ssa_var_key(addr);
                    if pointer_vars.contains(&addr_key) {
                        widths.entry(addr_key).or_default().insert(val.size);
                    }
                    if let Some(slot) = stack_addr_slots.get(&ssa_var_block_key(block.addr, addr)) {
                        let val_key = ssa_var_key(val);
                        if pointer_vars.contains(&val_key) {
                            stack_pointer_values
                                .entry(slot.clone())
                                .or_default()
                                .push(val_key);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    for values in stack_pointer_values.values_mut() {
        values.sort();
        values.dedup();
        for pair in values.windows(2) {
            let a = pair[0].clone();
            let b = pair[1].clone();
            adjacency.entry(a.clone()).or_default().insert(b.clone());
            adjacency.entry(b).or_default().insert(a);
        }
    }

    let mut queue = widths.keys().cloned().collect::<VecDeque<_>>();
    while let Some(key) = queue.pop_front() {
        let Some(current) = widths.get(&key).cloned() else {
            continue;
        };
        let Some(neighbors) = adjacency.get(&key) else {
            continue;
        };
        for neighbor in neighbors {
            let target = widths.entry(neighbor.clone()).or_default();
            let old_len = target.len();
            target.extend(current.iter().copied());
            if target.len() != old_len {
                queue.push_back(neighbor.clone());
            }
        }
    }

    widths
        .into_iter()
        .filter_map(|(key, widths)| {
            (widths.len() == 1).then(|| (key, widths.into_iter().next().unwrap_or(0)))
        })
        .filter(|(_, width)| *width > 0)
        .collect()
}

fn add_pointer_pointee_flow_edge(
    adjacency: &mut HashMap<String, HashSet<String>>,
    pointer_vars: &HashSet<String>,
    a: &SSAVar,
    b: &SSAVar,
) {
    let a_key = ssa_var_key(a);
    let b_key = ssa_var_key(b);
    if a_key == b_key || !pointer_vars.contains(&a_key) || !pointer_vars.contains(&b_key) {
        return;
    }
    adjacency
        .entry(a_key.clone())
        .or_default()
        .insert(b_key.clone());
    adjacency.entry(b_key).or_default().insert(a_key);
}

fn merge_width_hint(width_hints: &mut HashMap<String, u32>, var: &SSAVar, bits: u32) {
    let entry = width_hints.entry(ssa_var_key(var)).or_insert(0);
    *entry = (*entry).max(bits.max(var.size.saturating_mul(8)));
}

fn mark_scalar_var(
    vars: &mut HashSet<String>,
    width_hints: &mut HashMap<String, u32>,
    var: &SSAVar,
) {
    vars.insert(ssa_var_key(var));
    merge_width_hint(width_hints, var, var.size.saturating_mul(8));
}

fn infer_scalar_var_evidence_from_ssa(
    ssa_blocks: &[SSABlock],
) -> (
    HashSet<String>,
    HashSet<String>,
    HashSet<String>,
    HashMap<String, u32>,
) {
    let register_versions = collect_register_version_keys(ssa_blocks);
    let mut scalar_proven: HashSet<String> = HashSet::new();
    let mut scalar_likely: HashSet<String> = HashSet::new();
    let mut bool_like: HashSet<String> = HashSet::new();
    let mut width_hints: HashMap<String, u32> = HashMap::new();

    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::IntMult { a, b, .. }
                | SSAOp::IntDiv { a, b, .. }
                | SSAOp::IntSDiv { a, b, .. }
                | SSAOp::IntRem { a, b, .. }
                | SSAOp::IntSRem { a, b, .. }
                | SSAOp::IntAnd { a, b, .. }
                | SSAOp::IntOr { a, b, .. }
                | SSAOp::IntXor { a, b, .. }
                | SSAOp::IntLeft { a, b, .. }
                | SSAOp::IntRight { a, b, .. }
                | SSAOp::IntSRight { a, b, .. }
                | SSAOp::IntCarry { a, b, .. }
                | SSAOp::IntSCarry { a, b, .. }
                | SSAOp::IntSBorrow { a, b, .. } => {
                    mark_scalar_var(&mut scalar_proven, &mut width_hints, a);
                    mark_scalar_var(&mut scalar_proven, &mut width_hints, b);
                }
                SSAOp::IntNegate { src, .. }
                | SSAOp::IntNot { src, .. }
                | SSAOp::PopCount { src, .. }
                | SSAOp::Lzcount { src, .. } => {
                    mark_scalar_var(&mut scalar_proven, &mut width_hints, src);
                }
                SSAOp::PtrAdd { index, .. } | SSAOp::PtrSub { index, .. } => {
                    mark_scalar_var(&mut scalar_proven, &mut width_hints, index);
                }
                SSAOp::IntAdd { a, b, .. } | SSAOp::IntSub { a, b, .. } => {
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, a);
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, b);
                }
                SSAOp::BoolNot { dst, src } => {
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, src);
                    bool_like.insert(ssa_var_key(src));
                    bool_like.insert(ssa_var_key(dst));
                    merge_width_hint(&mut width_hints, dst, 1);
                }
                SSAOp::CBranch { cond, .. }
                | SSAOp::LoadGuarded { guard: cond, .. }
                | SSAOp::StoreGuarded { guard: cond, .. } => {
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, cond);
                    bool_like.insert(ssa_var_key(cond));
                    merge_width_hint(&mut width_hints, cond, 1);
                }
                SSAOp::FloatNeg { src, .. }
                | SSAOp::FloatAbs { src, .. }
                | SSAOp::FloatSqrt { src, .. }
                | SSAOp::Cast { src, .. } => {
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, src);
                }
                SSAOp::IntEqual { dst, a, b }
                | SSAOp::IntNotEqual { dst, a, b }
                | SSAOp::IntLess { dst, a, b }
                | SSAOp::IntSLess { dst, a, b }
                | SSAOp::IntLessEqual { dst, a, b }
                | SSAOp::IntSLessEqual { dst, a, b }
                | SSAOp::FloatEqual { dst, a, b }
                | SSAOp::FloatNotEqual { dst, a, b }
                | SSAOp::FloatLess { dst, a, b }
                | SSAOp::FloatLessEqual { dst, a, b } => {
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, a);
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, b);
                    bool_like.insert(ssa_var_key(dst));
                    merge_width_hint(&mut width_hints, dst, 1);
                }
                SSAOp::BoolAnd { dst, a, b }
                | SSAOp::BoolOr { dst, a, b }
                | SSAOp::BoolXor { dst, a, b } => {
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, a);
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, b);
                    bool_like.insert(ssa_var_key(a));
                    bool_like.insert(ssa_var_key(b));
                    bool_like.insert(ssa_var_key(dst));
                    merge_width_hint(&mut width_hints, dst, 1);
                }
                SSAOp::IntZExt { dst, src } | SSAOp::IntSExt { dst, src } => {
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, src);
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, dst);
                    merge_width_hint(&mut width_hints, dst, dst.size.saturating_mul(8));
                }
                SSAOp::Subpiece { dst, src, .. } => {
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, src);
                    mark_scalar_var(&mut scalar_likely, &mut width_hints, dst);
                    merge_width_hint(&mut width_hints, dst, dst.size.saturating_mul(8));
                }
                _ => {}
            }
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for block in ssa_blocks {
            for op in &block.ops {
                match op {
                    SSAOp::IntAdd { dst, a, b }
                    | SSAOp::IntSub { dst, a, b }
                    | SSAOp::IntMult { dst, a, b }
                    | SSAOp::IntDiv { dst, a, b }
                    | SSAOp::IntSDiv { dst, a, b }
                    | SSAOp::IntRem { dst, a, b }
                    | SSAOp::IntSRem { dst, a, b }
                    | SSAOp::IntAnd { dst, a, b }
                    | SSAOp::IntOr { dst, a, b }
                    | SSAOp::IntXor { dst, a, b }
                    | SSAOp::IntLeft { dst, a, b }
                    | SSAOp::IntRight { dst, a, b }
                    | SSAOp::IntSRight { dst, a, b } => {
                        let dst_key = ssa_var_key(dst);
                        let a_key = ssa_var_key(a);
                        let b_key = ssa_var_key(b);
                        let any_proven =
                            scalar_proven.contains(&a_key) || scalar_proven.contains(&b_key);
                        let any_likely = scalar_likely.contains(&a_key)
                            || scalar_likely.contains(&b_key)
                            || any_proven;
                        if any_proven {
                            changed |= scalar_proven.insert(dst_key.clone());
                        }
                        if any_likely {
                            changed |= scalar_likely.insert(dst_key.clone());
                        }
                        let operand_bits = [a, b]
                            .into_iter()
                            .filter(|var| !ssa_var_is_const(var))
                            .filter_map(|var| width_hints.get(&ssa_var_key(var)).copied())
                            .filter(|bits| *bits > 0)
                            .max()
                            .unwrap_or(0);
                        if operand_bits > 0 {
                            let entry = width_hints.entry(dst_key).or_insert(0);
                            if operand_bits > *entry {
                                *entry = operand_bits;
                                changed = true;
                            }
                        }
                    }
                    SSAOp::Phi { dst, sources } => {
                        let dst_key = ssa_var_key(dst);
                        let any_proven = sources
                            .iter()
                            .any(|src| scalar_proven.contains(&ssa_var_key(src)));
                        let any_likely = sources
                            .iter()
                            .any(|src| scalar_likely.contains(&ssa_var_key(src)));
                        let any_bool = sources
                            .iter()
                            .any(|src| bool_like.contains(&ssa_var_key(src)));
                        if any_proven {
                            changed |= scalar_proven.insert(dst_key.clone());
                        }
                        if any_likely || any_proven {
                            changed |= scalar_likely.insert(dst_key.clone());
                        }
                        if any_bool {
                            changed |= bool_like.insert(dst_key.clone());
                        }
                        let max_bits = sources
                            .iter()
                            .filter_map(|src| width_hints.get(&ssa_var_key(src)).copied())
                            .max()
                            .unwrap_or(0);
                        if max_bits > 0 {
                            let entry = width_hints.entry(dst_key).or_insert(0);
                            if max_bits > *entry {
                                *entry = max_bits;
                                changed = true;
                            }
                        }
                    }
                    SSAOp::Copy { dst, src }
                    | SSAOp::Cast { dst, src }
                    | SSAOp::New { dst, src } => {
                        let dst_key = ssa_var_key(dst);
                        let src_key = ssa_var_key(src);
                        if scalar_proven.contains(&src_key) {
                            changed |= scalar_proven.insert(dst_key.clone());
                        }
                        if scalar_likely.contains(&src_key) || scalar_proven.contains(&src_key) {
                            changed |= scalar_likely.insert(dst_key.clone());
                        }
                        if bool_like.contains(&src_key) {
                            changed |= bool_like.insert(dst_key.clone());
                        }
                        let bits = width_hints.get(&src_key).copied().unwrap_or(0);
                        if bits > 0 {
                            let entry = width_hints.entry(dst_key).or_insert(0);
                            if bits > *entry {
                                *entry = bits;
                                changed = true;
                            }
                        }
                    }
                    SSAOp::IntZExt { dst, src }
                    | SSAOp::IntSExt { dst, src }
                    | SSAOp::Subpiece { dst, src, .. } => {
                        let dst_key = ssa_var_key(dst);
                        let src_key = ssa_var_key(src);
                        if scalar_likely.contains(&src_key) || scalar_proven.contains(&src_key) {
                            changed |= scalar_likely.insert(dst_key.clone());
                        }
                        if bool_like.contains(&src_key) {
                            changed |= bool_like.insert(dst_key.clone());
                        }
                        let entry = width_hints.entry(dst_key).or_insert(0);
                        let bits = dst.size.saturating_mul(8);
                        if bits > *entry {
                            *entry = bits;
                            changed = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        for reg_keys in register_versions.values() {
            let any_proven = reg_keys.iter().any(|key| scalar_proven.contains(key));
            let any_likely = reg_keys.iter().any(|key| scalar_likely.contains(key));
            let any_bool = reg_keys.iter().any(|key| bool_like.contains(key));
            let max_bits = reg_keys
                .iter()
                .filter_map(|key| width_hints.get(key).copied())
                .max()
                .unwrap_or(0);
            let min_bits = reg_keys
                .iter()
                .filter_map(|key| width_hints.get(key).copied())
                .filter(|bits| *bits > 0)
                .min()
                .unwrap_or(0);
            let preferred_bits = if min_bits > 0 && max_bits == 64 && min_bits <= 32 {
                min_bits
            } else {
                max_bits
            };
            for key in reg_keys {
                if any_proven {
                    changed |= scalar_proven.insert(key.clone());
                }
                if any_likely || any_proven {
                    changed |= scalar_likely.insert(key.clone());
                }
                if any_bool {
                    changed |= bool_like.insert(key.clone());
                }
                if preferred_bits > 0 {
                    let entry = width_hints.entry(key.clone()).or_insert(0);
                    if preferred_bits > *entry {
                        *entry = preferred_bits;
                        changed = true;
                    }
                }
            }
        }
    }

    (scalar_proven, scalar_likely, bool_like, width_hints)
}

fn infer_usage_register_type_hints(
    ssa_blocks: &[SSABlock],
) -> (HashMap<String, TypeHint>, HashSet<String>) {
    let pointer_vars = infer_pointer_var_keys_from_ssa(ssa_blocks);
    let mut hints = HashMap::new();

    for block in ssa_blocks {
        for op in &block.ops {
            let mut maybe_add = |var: &SSAVar| {
                let key = ssa_var_key(var);
                if !pointer_vars.contains(&key) || !ssa_var_is_register_like(var) {
                    return;
                }
                merge_type_hint(
                    &mut hints,
                    var.name.to_ascii_lowercase(),
                    TypeHint::pointer(),
                );
            };
            if let Some(dst) = op.dst() {
                maybe_add(dst);
            }
            op.for_each_source(&mut maybe_add);
        }
    }

    (hints, pointer_vars)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn metadata_scalar_type_hints_are_width_aware() {
        assert_eq!(
            scalar_metadata_type_hint(MetadataScalarKind::Bool, 1).map(|hint| hint.ty),
            Some("bool".to_string())
        );
        assert_eq!(
            scalar_metadata_type_hint(MetadataScalarKind::SignedInt, 4).map(|hint| hint.ty),
            Some("int32_t".to_string())
        );
        assert_eq!(
            scalar_metadata_type_hint(MetadataScalarKind::UnsignedInt, 8).map(|hint| hint.ty),
            Some("uint64_t".to_string())
        );
        assert_eq!(
            scalar_metadata_type_hint(MetadataScalarKind::Float, 8).map(|hint| hint.ty),
            Some("double".to_string())
        );
        assert!(scalar_metadata_type_hint(MetadataScalarKind::Unknown, 8).is_none());
    }

    #[test]
    fn value_metadata_pointer_hint_overrides_scalar_hint() {
        let hint = type_hint_from_value_metadata(true, Some(MetadataScalarKind::UnsignedInt), 8)
            .expect("pointer hint");

        assert_eq!(hint.rank, TypeHintRank::Pointer);
        assert_eq!(hint.ty, "void *");
    }

    #[test]
    fn register_like_filter_rejects_non_register_ssa_names() {
        let cases = [
            ("rax", true),
            ("reg:10", true),
            ("tmp:0x1000", false),
            ("const:0x42", false),
            ("CONST:0x42", false),
            ("ram:0x401000", false),
            ("space1:0x20", false),
            ("sym.main", false),
            ("obj.global", false),
            ("data.rel.ro", false),
            ("got.printf", false),
        ];

        for (name, expected) in cases {
            let var = SSAVar::new(name, 0, 8);
            assert_eq!(ssa_var_is_register_like(&var), expected, "{name}");
        }
    }

    #[test]
    fn recovered_signature_params_follow_x86_64_arch_profile() {
        let block = SSABlock {
            addr: 0x401000,
            size: 4,
            ops: vec![SSAOp::Copy {
                dst: SSAVar::new("tmp:0", 1, 8),
                src: SSAVar::new("rdi", 0, 8),
            }],
        };

        let params =
            recover_signature_params_from_ssa(&[block], Some("x86-64"), &HashMap::new(), true, 64);

        assert_eq!(params.len(), 1);
        assert_eq!(params[0].name, "arg0");
        assert_eq!(params[0].ssa_var, SSAVar::new("rdi", 0, 8));
        assert_eq!(
            params[0].initial_ty,
            crate::CTypeLike::Int {
                bits: 64,
                signedness: crate::Signedness::Signed,
            }
        );
    }

    #[test]
    fn recovered_argument_keeps_version_zero_subregister_width() {
        let block = SSABlock {
            addr: 0x401000,
            size: 8,
            ops: vec![
                SSAOp::Copy {
                    dst: SSAVar::new("tmp:value", 1, 4),
                    src: SSAVar::new("EDX", 0, 4),
                },
                SSAOp::IntSExt {
                    dst: SSAVar::new("RDX", 1, 8),
                    src: SSAVar::new("tmp:value", 1, 4),
                },
                SSAOp::IntMult {
                    dst: SSAVar::new("RDX", 2, 8),
                    a: SSAVar::new("RDX", 1, 8),
                    b: SSAVar::new("const:38", 0, 8),
                },
            ],
        };

        let params = recover_signature_params_from_ssa(
            std::slice::from_ref(&block),
            Some("x86-64"),
            &HashMap::new(),
            true,
            64,
        );
        let param = params
            .iter()
            .find(|param| param.name == "arg2")
            .expect("third parameter");
        assert_eq!(
            param.initial_ty,
            crate::CTypeLike::Int {
                bits: 32,
                signedness: crate::Signedness::Signed,
            }
        );

        let vars = recover_vars_from_ssa(&[block], Some("x86-64"), &HashMap::new(), true);
        let var = vars
            .iter()
            .find(|var| var.name == "arg2")
            .expect("third recovered variable");
        assert_eq!(var.var_type, "int32_t");
    }

    #[test]
    fn recovered_signature_params_include_x86_64_stack_pointer_args() {
        let block = SSABlock {
            addr: 0x401000,
            size: 12,
            ops: vec![
                SSAOp::Copy {
                    dst: SSAVar::new("tmp:0", 1, 8),
                    src: SSAVar::new("rdi", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:sp8", 1, 8),
                    a: SSAVar::new("rsp", 0, 8),
                    b: SSAVar::new("const:0x8", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:stack_arg", 1, 8),
                    addr: SSAVar::new("tmp:sp8", 1, 8),
                    space: "ram".to_string(),
                },
            ],
        };

        let params =
            recover_signature_params_from_ssa(&[block], Some("x86-64"), &HashMap::new(), true, 64);

        assert_eq!(params.len(), 2);
        assert_eq!(params[0].name, "arg0");
        assert_eq!(params[0].ssa_var, SSAVar::new("rdi", 0, 8));
        assert_eq!(params[1].name, "arg6");
        assert_eq!(params[1].ssa_var, SSAVar::new("tmp:stack_arg", 1, 8));
        assert_eq!(
            params[1].initial_ty,
            crate::CTypeLike::Int {
                bits: 64,
                signedness: crate::Signedness::Signed,
            }
        );
    }

    #[test]
    fn recovered_signature_params_follow_pointer_through_stack_home_and_indexed_load() {
        let entry = SSABlock {
            addr: 0x401000,
            size: 8,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:home", 1, 8),
                    a: SSAVar::new("rbp", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("tmp:saved_arg", 1, 8),
                    src: SSAVar::new("rdi", 0, 8),
                },
                SSAOp::Store {
                    addr: SSAVar::new("tmp:home", 1, 8),
                    val: SSAVar::new("tmp:saved_arg", 1, 8),
                    space: "ram".to_string(),
                },
            ],
        };
        let body = SSABlock {
            addr: 0x401010,
            size: 8,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:home_reload", 1, 8),
                    a: SSAVar::new("rbp", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:base", 1, 8),
                    addr: SSAVar::new("tmp:home_reload", 1, 8),
                    space: "ram".to_string(),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("rax", 3, 8),
                    src: SSAVar::new("tmp:base", 1, 8),
                },
                SSAOp::IntSExt {
                    dst: SSAVar::new("rcx", 2, 8),
                    src: SSAVar::new("tmp:index", 1, 4),
                },
                SSAOp::IntMult {
                    dst: SSAVar::new("tmp:scaled", 1, 8),
                    a: SSAVar::new("rcx", 2, 8),
                    b: SSAVar::new("const:4", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:element", 1, 8),
                    a: SSAVar::new("rax", 3, 8),
                    b: SSAVar::new("tmp:scaled", 1, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:value", 1, 4),
                    addr: SSAVar::new("tmp:element", 1, 8),
                    space: "ram".to_string(),
                },
            ],
        };

        let params = recover_signature_params_from_ssa(
            &[entry, body],
            Some("x86-64"),
            &HashMap::new(),
            false,
            64,
        );
        let arg0 = params
            .iter()
            .find(|param| param.name == "arg0")
            .expect("rdi argument");

        assert_eq!(
            crate::render_signature_type(&arg0.initial_ty, 64),
            "int32_t*"
        );
    }

    #[test]
    fn recover_vars_from_ssa_marks_x86_64_stack_pointer_arg_slot() {
        let block = SSABlock {
            addr: 0x401000,
            size: 8,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:sp8", 1, 8),
                    a: SSAVar::new("rsp", 0, 8),
                    b: SSAVar::new("const:0x8", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:stack_arg", 1, 8),
                    addr: SSAVar::new("tmp:sp8", 1, 8),
                    space: "ram".to_string(),
                },
            ],
        };

        let vars = recover_vars_from_ssa(&[block], Some("x86-64"), &HashMap::new(), true);
        let stack_arg = vars
            .iter()
            .find(|var| var.kind == "s" && var.delta == 8)
            .expect("rsp+8 should be recovered as an incoming stack argument");

        assert_eq!(stack_arg.name, "arg6");
        assert!(stack_arg.isarg);
        assert_eq!(stack_arg.var_type, "int64_t");
    }

    #[test]
    fn recover_vars_from_ssa_does_not_treat_epilogue_stack_as_incoming_args() {
        let block = SSABlock {
            addr: 0x401000,
            size: 8,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("rsp", 2, 8),
                    a: SSAVar::new("rsp", 1, 8),
                    b: SSAVar::new("const:0x8", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("rip", 1, 8),
                    addr: SSAVar::new("rsp", 2, 8),
                    space: "ram".to_string(),
                },
                SSAOp::Return {
                    target: SSAVar::new("rip", 1, 8),
                },
            ],
        };

        let vars = recover_vars_from_ssa(&[block], Some("x86-64"), &HashMap::new(), true);

        assert!(vars.iter().all(|var| !var.isarg));
        assert!(vars.iter().all(|var| var.delta != 8));
        assert!(collect_pointer_arg_slots(&vars).is_empty());
    }

    #[test]
    fn recover_vars_from_ssa_rejects_constant_minus_stack_pointer_as_an_address() {
        let block = SSABlock {
            addr: 0x401000,
            size: 8,
            ops: vec![
                SSAOp::IntSub {
                    dst: SSAVar::new("tmp:not_stack", 1, 8),
                    a: SSAVar::new("const:0x20", 0, 8),
                    b: SSAVar::new("rsp", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:value", 1, 8),
                    addr: SSAVar::new("tmp:not_stack", 1, 8),
                    space: "ram".to_string(),
                },
            ],
        };

        let vars = recover_vars_from_ssa(&[block], Some("x86-64"), &HashMap::new(), true);

        assert!(vars.is_empty());
    }

    #[test]
    fn recovered_signature_params_follow_arm64_arch_profile() {
        let block = SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![SSAOp::Copy {
                dst: SSAVar::new("tmp:0", 1, 8),
                src: SSAVar::new("x1", 0, 8),
            }],
        };

        let params =
            recover_signature_params_from_ssa(&[block], Some("aarch64"), &HashMap::new(), true, 64);

        assert_eq!(params.len(), 1);
        assert_eq!(params[0].name, "arg1");
        assert_eq!(params[0].ssa_var, SSAVar::new("x1", 0, 8));
    }
}
