use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use r2ssa::{
    DecompilePrepFacts, SSABlock, SSAOp, SSAVar, SSAVarNameKind, SsaArtifact, StackAddressBase,
};

use crate::parse_c_type_like;
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
    architecture: r2ssa::MachineArchitectureFamily,
) -> (ArgAliasMap, BaseRegList, BaseRegList) {
    use r2ssa::MachineArchitectureFamily;

    match architecture {
        MachineArchitectureFamily::X86 => (&[], X86_STACK_BASES, X86_FRAME_BASES),
        MachineArchitectureFamily::X86_64 => (X86_ARG_REGS, X86_STACK_BASES, X86_FRAME_BASES),
        MachineArchitectureFamily::Arm => (ARM32_ARG_REGS, ARM32_STACK_BASES, ARM32_FRAME_BASES),
        MachineArchitectureFamily::AArch64 => {
            (ARM64_ARG_REGS, ARM64_STACK_BASES, ARM64_FRAME_BASES)
        }
        MachineArchitectureFamily::RiscV32 | MachineArchitectureFamily::RiscV64 => {
            (RISCV_ARG_REGS, RISCV_STACK_BASES, RISCV_FRAME_BASES)
        }
        MachineArchitectureFamily::Mips32 | MachineArchitectureFamily::Mips64 => {
            (MIPS_ARG_REGS, MIPS_STACK_BASES, MIPS_FRAME_BASES)
        }
        MachineArchitectureFamily::PowerPc32
        | MachineArchitectureFamily::PowerPc64
        | MachineArchitectureFamily::Unknown => (&[], GENERIC_STACK_BASES, GENERIC_FRAME_BASES),
    }
}

pub(crate) fn legacy_architecture_family(
    arch_name: Option<&str>,
) -> r2ssa::MachineArchitectureFamily {
    use r2ssa::MachineArchitectureFamily;

    match arch_name
        .map(str::trim)
        .map(str::to_ascii_lowercase)
        .as_deref()
    {
        Some("x86") | Some("x86-32") | Some("i386") | Some("i686") => {
            MachineArchitectureFamily::X86
        }
        Some("x86-64") | Some("x86_64") | Some("x64") | Some("amd64") => {
            MachineArchitectureFamily::X86_64
        }
        Some("arm") => MachineArchitectureFamily::Arm,
        Some("aarch64") | Some("arm64") => MachineArchitectureFamily::AArch64,
        Some("riscv32") | Some("rv32") => MachineArchitectureFamily::RiscV32,
        Some("riscv64") | Some("rv64") => MachineArchitectureFamily::RiscV64,
        Some("mips") | Some("mips32") => MachineArchitectureFamily::Mips32,
        Some("mips64") => MachineArchitectureFamily::Mips64,
        Some("ppc") | Some("powerpc") | Some("powerpc32") => MachineArchitectureFamily::PowerPc32,
        Some("ppc64") | Some("powerpc64") => MachineArchitectureFamily::PowerPc64,
        _ => MachineArchitectureFamily::Unknown,
    }
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
                && let Some(offset) = b.constant_bits()
            {
                return Some((dst, a, offset as i64));
            }
            if stack_bases.contains(&b.name.to_ascii_lowercase().as_str())
                && let Some(offset) = a.constant_bits()
            {
                return Some((dst, b, offset as i64));
            }
            None
        }
        SSAOp::IntSub { dst, a, b } => {
            if stack_bases.contains(&a.name.to_ascii_lowercase().as_str())
                && let Some(offset) = b.constant_bits()
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

/// A key that identifies one SSA variable across its width views.
///
/// This deliberately does *not* include `size`. The maps it keys pool the
/// register's width views on purpose -- arm64 evidence has to flow between
/// `x0` and `w0`, and the x86 low-carrier tests fail immediately if it cannot.
///
/// It does now include `rename_disambiguator`, which it dropped before. That
/// field exists, by its own documentation, to separate "two exact source
/// storages that project to the same display name and width", so leaving it out
/// made the key collide on precisely the case it had been added to prevent, and
/// `DefUseInfo` carried the resulting ambiguity at runtime as an
/// `Option<usize>` meaning "the key collided". Width views of one register
/// share a disambiguator, so pooling still works.
pub fn ssa_var_key(var: &SSAVar) -> String {
    format!(
        "{}_{}_{}",
        var.name.to_ascii_lowercase(),
        var.version,
        var.rename_disambiguator()
    )
}

pub fn ssa_var_block_key(block_addr: u64, var: &SSAVar) -> String {
    format!("{}@{block_addr:x}", ssa_var_key(var))
}

/// Whether a key names the given register family at the given version.
///
/// This lives beside `ssa_var_key` because it takes the key apart, and a
/// builder and a parser that disagree about a format are the same defect twice.
/// It used to be a `rsplit_once('_')` in `signature_infer`, which silently began
/// reading the disambiguator as the version the moment the key gained a field.
/// The variable name a key was built from.
pub fn ssa_var_key_name(key: &str) -> Option<&str> {
    let mut parts = key.rsplitn(3, '_');
    parts.next()?;
    parts.next()?;
    parts.next()
}

pub fn ssa_var_key_matches_register_family_version(key: &str, family: &str, version: u32) -> bool {
    // Built as `name_version_disambiguator`, and a name may itself contain
    // underscores, so the three fields are taken from the right.
    let mut parts = key.rsplitn(3, '_');
    let Some(_disambiguator) = parts.next() else {
        return false;
    };
    let Some(version_str) = parts.next() else {
        return false;
    };
    let Some(name) = parts.next() else {
        return false;
    };
    version_str.parse::<u32>().ok() == Some(version) && scalar_register_family_key(name) == family
}

pub fn scalar_register_family_key(name: &str) -> String {
    let lower = name.to_ascii_lowercase();
    let x86_family = match lower.as_str() {
        "rax" | "eax" | "ax" | "al" | "ah" => Some("ax"),
        "rbx" | "ebx" | "bx" | "bl" | "bh" => Some("bx"),
        "rcx" | "ecx" | "cx" | "cl" | "ch" => Some("cx"),
        "rdx" | "edx" | "dx" | "dl" | "dh" => Some("dx"),
        "rsi" | "esi" | "si" | "sil" => Some("si"),
        "rdi" | "edi" | "di" | "dil" => Some("di"),
        "rbp" | "ebp" | "bp" | "bpl" => Some("bp"),
        "rsp" | "esp" | "spl" => Some("sp"),
        "r8" | "r8d" | "r8w" | "r8b" => Some("8"),
        "r9" | "r9d" | "r9w" | "r9b" => Some("9"),
        "r10" | "r10d" | "r10w" | "r10b" => Some("10"),
        "r11" | "r11d" | "r11w" | "r11b" => Some("11"),
        "r12" | "r12d" | "r12w" | "r12b" => Some("12"),
        "r13" | "r13d" | "r13w" | "r13b" => Some("13"),
        "r14" | "r14d" | "r14w" | "r14b" => Some("14"),
        "r15" | "r15d" | "r15w" | "r15b" => Some("15"),
        _ => None,
    };
    if let Some(family) = x86_family {
        return format!("x86:gpr:{family}");
    }

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
    collect_signature_type_evidence_context_with_arch(ssa_blocks, None)
}

pub fn collect_signature_type_evidence_context_with_arch(
    ssa_blocks: &[SSABlock],
    arch_name: Option<&str>,
) -> SignatureTypeEvidenceContext {
    let (_, stack_bases, _) = recover_vars_arch_profile(legacy_architecture_family(arch_name));
    let pointer_vars = infer_pointer_var_keys_from_ssa(ssa_blocks, stack_bases);
    let pointer_pointee_width_bytes =
        infer_pointer_pointee_width_bytes(ssa_blocks, &pointer_vars, stack_bases);
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

pub fn recover_signature_params_from_ssa(
    ssa_blocks: &[SSABlock],
    arch_name: Option<&str>,
    metadata_reg_type_hints: &HashMap<String, TypeHint>,
    semantic_metadata_enabled: bool,
    ptr_bits: u32,
) -> Vec<RecoveredSignatureParam> {
    let (arg_regs, _, _) = recover_vars_arch_profile(legacy_architecture_family(arch_name));
    if arg_regs.is_empty() {
        return Vec::new();
    }

    let signature_evidence =
        collect_signature_type_evidence_context_with_arch(ssa_blocks, arch_name);
    let (usage_reg_type_hints, _pointer_var_keys) =
        infer_usage_register_type_hints(ssa_blocks, arch_name);
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
                SSAOp::Load {
                    dst,
                    space: r2il::SpaceId::Ram,
                    addr,
                } => {
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
                            .and_then(|ty| parse_c_type_like(ty, ptr_bits))
                            .unwrap_or_else(|| size_to_neutral_int_type_like(dst.size));
                        params.push(RecoveredSignatureParam {
                            name: format!("arg{index}"),
                            arg_index: index,
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
                        enabled_metadata_hints,
                        canonical,
                        aliases,
                        src,
                        Some(&signature_evidence),
                        ptr_bits,
                    );
                    let initial_ty = hinted_type
                        .map(|hint| hint.ty)
                        .unwrap_or_else(|| size_to_neutral_int_type_like(src.size));
                    params.push(RecoveredSignatureParam {
                        name: format!("arg{index}"),
                        arg_index: index,
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

fn prepared_formal_parameters(prepared: &r2ssa::SsaArtifact) -> BTreeMap<usize, SSAVar> {
    let mut parameters = BTreeMap::<usize, SSAVar>::new();
    for (index, fact) in &prepared.facts().boundaries.parameters {
        if fact.index != *index {
            continue;
        }
        let Some(var) = prepared.value_var(fact.value) else {
            continue;
        };
        parameters.insert(*index as usize, var.clone());
    }
    parameters
}

pub(crate) fn recover_signature_params_from_prepared_ssa(
    prepared: &r2ssa::SsaArtifact,
    ptr_bits: u32,
) -> Vec<RecoveredSignatureParam> {
    prepared_formal_parameters(prepared)
        .into_iter()
        .map(|(index, var)| {
            let initial_ty = if source_parameter_is_logical_pointer(prepared, index, ptr_bits)
                || source_parameter_has_certified_memory_use(prepared, index)
            {
                crate::CTypeLike::Pointer(Box::new(crate::CTypeLike::Void))
            } else {
                size_to_neutral_int_type_like(var.size)
            };
            RecoveredSignatureParam {
                name: format!("arg{index}"),
                arg_index: index,
                ssa_var: var,
                initial_ty: if matches!(initial_ty, crate::CTypeLike::Unknown) && ptr_bits > 0 {
                    crate::CTypeLike::Int {
                        bits: ptr_bits,
                        signedness: crate::Signedness::Unknown,
                    }
                } else {
                    initial_ty
                },
            }
        })
        .collect()
}

fn source_parameter_is_logical_pointer(
    prepared: &r2ssa::SsaArtifact,
    index: usize,
    ptr_bits: u32,
) -> bool {
    let context = prepared.machine_context();
    if !context.abi_model().is_available() {
        return false;
    }
    let Some(interface) = context.function_interface() else {
        return false;
    };
    let Some(graph) = interface
        .type_graph()
        .filter(|graph| graph.validates_pointer_width(ptr_bits))
    else {
        return false;
    };
    let Some(parameter) = prepared
        .facts()
        .boundaries
        .parameters
        .get(&u32::try_from(index).unwrap_or(u32::MAX))
    else {
        return false;
    };
    if parameter.index as usize != index {
        return false;
    }
    let Some(logical_value) = parameter.logical_value else {
        return false;
    };
    graph
        .types()
        .get(logical_value.type_id() as usize)
        .is_some_and(|source_type| {
            matches!(source_type.kind(), r2ssa::SourceTypeKind::Pointer { .. })
        })
}

fn source_parameter_has_certified_memory_use(prepared: &r2ssa::SsaArtifact, index: usize) -> bool {
    prepared
        .certificates()
        .memory_accesses
        .values()
        .filter(|access| {
            access.space == r2il::SpaceId::Ram
                && prepared
                    .machine_context()
                    .memory_space_at(access.block_addr, access.op_index)
                    == Some(access.space)
        })
        .any(|access| {
            prepared
                .addresses()
                .parameter_expression(access.address)
                .is_some_and(|address| address.parameter == index)
        })
}

pub(crate) fn prepared_arch_name(prepared: &r2ssa::SsaArtifact) -> Option<&'static str> {
    match prepared.machine_context().architecture_family() {
        r2ssa::MachineArchitectureFamily::X86 => Some("x86"),
        r2ssa::MachineArchitectureFamily::X86_64 => Some("x86-64"),
        r2ssa::MachineArchitectureFamily::Arm => Some("arm"),
        r2ssa::MachineArchitectureFamily::AArch64 => Some("aarch64"),
        r2ssa::MachineArchitectureFamily::RiscV32 => Some("riscv32"),
        r2ssa::MachineArchitectureFamily::RiscV64 => Some("riscv64"),
        r2ssa::MachineArchitectureFamily::Mips32 => Some("mips"),
        r2ssa::MachineArchitectureFamily::Mips64 => Some("mips64"),
        r2ssa::MachineArchitectureFamily::PowerPc32 => Some("powerpc"),
        r2ssa::MachineArchitectureFamily::PowerPc64 => Some("powerpc64"),
        r2ssa::MachineArchitectureFamily::Unknown => None,
    }
}

fn prepared_register_name(prepared: &r2ssa::SsaArtifact, index: usize) -> Option<String> {
    let slot = prepared
        .machine_context()
        .abi_model()
        .argument_registers()
        .iter()
        .find(|slot| slot.index() as usize == index)?;
    prepared
        .machine_context()
        .register_storages_by_name()
        .iter()
        .filter(|(_, storage)| **storage == slot.storage())
        .map(|(name, _)| name)
        .min_by_key(|name| (name.len(), *name))
        .cloned()
}

pub(crate) fn recover_vars_from_prepared_ssa(
    prepared: &r2ssa::SsaArtifact,
    ptr_bits: u32,
) -> Vec<RecoveredVariable> {
    let mut vars = recover_signature_params_from_prepared_ssa(prepared, ptr_bits)
        .into_iter()
        .map(|parameter| RecoveredVariable {
            name: parameter.name,
            kind: "r".to_string(),
            delta: 0,
            var_type: match parameter.initial_ty {
                crate::CTypeLike::Pointer(_) => "void *".to_string(),
                _ => size_to_type(parameter.ssa_var.size),
            },
            isarg: true,
            reg: prepared_register_name(prepared, parameter.arg_index),
        })
        .collect::<Vec<_>>();

    let mut stack_slots = prepared
        .certificates()
        .stack_slots
        .values()
        .map(|slot| {
            let size = slot.size.unwrap_or_else(|| {
                prepared
                    .certificates()
                    .memory_accesses
                    .values()
                    .filter(|access| access.object == slot.object)
                    .map(|access| access.width)
                    .max()
                    .unwrap_or(0)
            });
            RecoveredVariable {
                name: if slot.offset < 0 {
                    format!("var_{:x}", slot.offset.unsigned_abs())
                } else {
                    format!("var_{}", slot.offset)
                },
                kind: "v".to_string(),
                delta: slot.offset,
                var_type: size_to_type(size),
                isarg: false,
                reg: None,
            }
        })
        .collect::<Vec<_>>();
    vars.append(&mut stack_slots);
    vars.sort_by(|left, right| {
        left.isarg
            .cmp(&right.isarg)
            .reverse()
            .then_with(|| left.delta.cmp(&right.delta))
            .then_with(|| left.name.cmp(&right.name))
    });
    vars.dedup_by(|left, right| {
        left.isarg == right.isarg
            && left.delta == right.delta
            && left.reg == right.reg
            && left.name == right.name
    });
    vars
}

pub fn recover_vars_from_ssa(
    ssa_blocks: &[SSABlock],
    arch_name: Option<&str>,
    metadata_reg_type_hints: &HashMap<String, TypeHint>,
    semantic_metadata_enabled: bool,
) -> Vec<RecoveredVariable> {
    recover_vars_from_ssa_with_prep_facts(
        ssa_blocks,
        None,
        arch_name,
        metadata_reg_type_hints,
        semantic_metadata_enabled,
    )
}

pub fn recover_vars_from_ssa_with_prep_facts(
    ssa_blocks: &[SSABlock],
    prep_facts: Option<&DecompilePrepFacts>,
    arch_name: Option<&str>,
    metadata_reg_type_hints: &HashMap<String, TypeHint>,
    semantic_metadata_enabled: bool,
) -> Vec<RecoveredVariable> {
    let mut vars = Vec::new();
    let mut seen_slots: HashMap<(bool, i64), usize> = HashMap::new();
    let mut seen_arg_regs: HashSet<String> = HashSet::new();
    let (arg_regs, stack_bases, frame_bases) =
        recover_vars_arch_profile(legacy_architecture_family(arch_name));
    let ptr_bits = if arch_is_x86_64_sysv_like(arch_name) {
        64
    } else {
        0
    };
    let signature_evidence =
        collect_signature_type_evidence_context_with_arch(ssa_blocks, arch_name);
    let (usage_reg_type_hints, pointer_var_keys) =
        infer_usage_register_type_hints(ssa_blocks, arch_name);
    let empty_metadata_hints = HashMap::new();
    let enabled_metadata_hints = if semantic_metadata_enabled {
        metadata_reg_type_hints
    } else {
        &empty_metadata_hints
    };
    let reg_type_hints =
        merge_register_type_hints(enabled_metadata_hints, &usage_reg_type_hints, arg_regs);

    let mut stack_addr_temps: HashMap<String, (SSAVar, i64, bool)> = HashMap::new();
    let control_return_targets = collect_control_return_targets(ssa_blocks);

    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::IntAdd { dst, .. } | SSAOp::IntSub { dst, .. } => {
                    if let Some((_, base, raw_offset)) = stack_addr_temp(op, stack_bases) {
                        let canonical_root = prep_facts
                            .and_then(|facts| facts.stack_address_root_of(dst))
                            .copied();
                        let offset = canonical_root.map(|root| root.offset).unwrap_or(raw_offset);
                        let is_frame_base = canonical_root
                            .map(|root| matches!(root.base, StackAddressBase::FramePointer))
                            .unwrap_or_else(|| {
                                frame_bases.contains(&base.name.to_ascii_lowercase().as_str())
                            });
                        let dst_key = ssa_var_block_key(block.addr, dst);
                        stack_addr_temps.insert(dst_key, (base.clone(), offset, is_frame_base));
                    }
                }
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr,
                    val,
                } => {
                    let addr_key = ssa_var_block_key(block.addr, addr);
                    if let Some((base, offset, is_frame_base)) = stack_addr_temps.get(&addr_key) {
                        let type_override = if pointer_var_keys.contains(&ssa_var_key(val)) {
                            Some("void *".to_string())
                        } else {
                            None
                        };
                        add_stack_var(
                            &mut vars,
                            &mut seen_slots,
                            *is_frame_base,
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
                SSAOp::Load {
                    dst,
                    space: r2il::SpaceId::Ram,
                    addr,
                } => {
                    let addr_key = ssa_var_block_key(block.addr, addr);
                    if !control_return_targets.contains(&ssa_var_key(dst))
                        && let Some((base, offset, is_frame_base)) = stack_addr_temps.get(&addr_key)
                    {
                        let type_override = if pointer_var_keys.contains(&ssa_var_key(dst)) {
                            Some("void *".to_string())
                        } else {
                            None
                        };
                        add_stack_var(
                            &mut vars,
                            &mut seen_slots,
                            *is_frame_base,
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
                                enabled_metadata_hints,
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
                                var_type: hinted_type
                                    .map(|hint| hint.display)
                                    .unwrap_or_else(|| size_to_type(src.size)),
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

fn size_to_neutral_int_type_like(size: u32) -> crate::CTypeLike {
    let bits = match size {
        1 => 8,
        2 => 16,
        4 => 32,
        8 => 64,
        _ => return crate::CTypeLike::Unknown,
    };
    crate::CTypeLike::Int {
        bits,
        signedness: crate::Signedness::Unknown,
    }
}

fn incoming_hint_should_replace(current: &TypeHint, incoming: &TypeHint) -> bool {
    incoming.rank > current.rank || (incoming.rank == current.rank && incoming.ty < current.ty)
}

fn ssa_var_is_const(var: &SSAVar) -> bool {
    var.constant_bits().is_some()
}

pub(crate) fn ssa_var_is_register_like(var: &SSAVar) -> bool {
    matches!(
        var.name_kind(),
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
    ssa_var_key_name(key).is_some_and(|name| scalar_register_family_key(name) == family)
}

fn width_hint_key_matches_family_version(key: &str, family: &str, version: u32) -> bool {
    ssa_var_key_matches_register_family_version(key, family, version)
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

struct RecoveredArgTypeHint {
    ty: crate::CTypeLike,
    display: String,
}

fn recovered_arg_type_hint(
    reg_type_hints: &HashMap<String, TypeHint>,
    metadata_reg_type_hints: &HashMap<String, TypeHint>,
    canonical: &str,
    aliases: &[&str],
    src: &SSAVar,
    signature_evidence: Option<&SignatureTypeEvidenceContext>,
    ptr_bits: u32,
) -> Option<RecoveredArgTypeHint> {
    let best_hint = strongest_hint_for_aliases(reg_type_hints, canonical, aliases);
    if let Some(hint) = best_hint.as_ref()
        && hint.rank == TypeHintRank::Pointer
    {
        let parsed = parse_c_type_like(&hint.ty, ptr_bits)?;
        if let Some(width) = signature_evidence.and_then(|evidence| {
            evidence
                .pointer_pointee_width_bytes
                .get(&ssa_var_key(src))
                .copied()
        }) {
            if matches!(
                parsed,
                crate::CTypeLike::Pointer(ref inner)
                    if !matches!(inner.as_ref(), crate::CTypeLike::Void | crate::CTypeLike::Unknown)
            ) {
                return Some(RecoveredArgTypeHint {
                    ty: parsed,
                    display: hint.ty.clone(),
                });
            }
            return Some(RecoveredArgTypeHint {
                ty: crate::CTypeLike::Pointer(Box::new(size_to_neutral_int_type_like(width))),
                display: format!("{} *", size_to_type(width)),
            });
        }
        return Some(RecoveredArgTypeHint {
            ty: parsed,
            display: hint.ty.clone(),
        });
    }
    if let Some(hint) = strongest_hint_for_aliases(metadata_reg_type_hints, canonical, aliases) {
        return explicit_arg_type_hint(&hint.ty, src, ptr_bits);
    }
    let bits =
        signature_evidence.and_then(|evidence| recovered_arg_family_width_hint(evidence, src))?;
    let width = bits.div_ceil(8).min(src.size);
    Some(RecoveredArgTypeHint {
        ty: size_to_neutral_int_type_like(width),
        display: size_to_type(width),
    })
}

fn explicit_arg_type_hint(hint: &str, src: &SSAVar, ptr_bits: u32) -> Option<RecoveredArgTypeHint> {
    match parse_c_type_like(hint, ptr_bits) {
        Some(crate::CTypeLike::Int {
            bits, signedness, ..
        }) if bits > src.size.saturating_mul(8) => Some(RecoveredArgTypeHint {
            ty: crate::CTypeLike::Int {
                bits: src.size.saturating_mul(8),
                signedness,
            },
            display: size_to_type(src.size),
        }),
        Some(ty) => Some(RecoveredArgTypeHint {
            ty,
            display: hint.to_string(),
        }),
        None => None,
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
    is_frame_base: bool,
    offset: i64,
    size: u32,
    hint: StackVarRecoveryHint,
) {
    let StackVarRecoveryHint {
        type_override,
        stack_arg_index,
    } = hint;
    let slot_key = (is_frame_base, offset);
    if let Some(existing_idx) = seen_slots.get(&slot_key).copied() {
        // A second hint for a slot that is already typed demotes it to the
        // opaque pointer, because the two disagree and neither is proven. The
        // comparison is on the types rather than on the spellings, so radare2
        // writing `void*` reaches the same conclusion as `void *`.
        if let Some(override_ty) = type_override
            && crate::parse_c_type_like(&override_ty, 64).is_some_and(|ty| ty.is_void_pointer())
            && let Some(existing) = vars.get_mut(existing_idx)
            && !existing.recovered_type_is_void_pointer()
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

fn collect_register_live_in_aliases(ssa_blocks: &[SSABlock]) -> Vec<(String, String)> {
    let mut last_definitions = HashMap::<String, SSAVar>::new();
    let mut aliases = Vec::new();
    for block in ssa_blocks {
        for op in &block.ops {
            op.for_each_source(|var| {
                if !ssa_var_is_register_like(var) {
                    return;
                }
                let family = scalar_register_family_key(&var.name);
                let source = ssa_var_key(var);
                if let Some(previous) = last_definitions.get(&family)
                    && var.version <= previous.version
                    && ssa_var_key(previous) != source
                {
                    aliases.push((ssa_var_key(previous), source));
                }
            });
            if let Some(dst) = op.dst()
                && ssa_var_is_register_like(dst)
            {
                last_definitions.insert(scalar_register_family_key(&dst.name), dst.clone());
            }
        }
    }
    aliases.sort();
    aliases.dedup();
    aliases
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

fn ssa_var_is_stack_base(var: &SSAVar, stack_bases: BaseRegList) -> bool {
    stack_bases.contains(&var.name.to_ascii_lowercase().as_str())
}

fn infer_pointer_width_bytes(ssa_blocks: &[SSABlock], stack_bases: BaseRegList) -> u32 {
    let mut width = 0u32;
    for block in ssa_blocks {
        for op in &block.ops {
            if let Some(dst) = op.dst()
                && ssa_var_is_stack_base(dst, stack_bases)
            {
                width = width.max(dst.size);
            }
            op.for_each_source(|src| {
                if ssa_var_is_stack_base(src, stack_bases) {
                    width = width.max(src.size);
                }
            });
        }
    }
    if width == 0 { 8 } else { width }
}

fn infer_index_like_var_keys(ssa_blocks: &[SSABlock]) -> HashSet<String> {
    let mut index_like: HashSet<String> = HashSet::new();
    let mut constant_like: HashSet<String> = HashSet::new();
    for block in ssa_blocks {
        for op in &block.ops {
            op.for_each_source(|source| {
                if ssa_var_is_const(source) {
                    constant_like.insert(ssa_var_key(source));
                }
            });
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
                        if constant_like.contains(&ssa_var_key(src)) {
                            changed |= constant_like.insert(ssa_var_key(dst));
                        }
                        if index_like.contains(&ssa_var_key(src)) {
                            changed |= index_like.insert(ssa_var_key(dst));
                        }
                    }
                    SSAOp::IntMult { dst, a, b } => {
                        let a_key = ssa_var_key(a);
                        let b_key = ssa_var_key(b);
                        let a_is_scaled_const = constant_like.contains(&a_key);
                        let b_is_scaled_const = constant_like.contains(&b_key);
                        let result_is_index = match (a_is_scaled_const, b_is_scaled_const) {
                            (true, false) | (false, true) => true,
                            (true, true) => {
                                index_like.contains(&a_key) || index_like.contains(&b_key)
                            }
                            (false, false) => false,
                        };
                        if result_is_index {
                            changed |= index_like.insert(ssa_var_key(dst));
                        }
                    }
                    SSAOp::IntLeft { dst, a, b } => {
                        let shift_amount = b.constant_bits().unwrap_or(u64::MAX);
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

fn infer_pointer_var_keys_from_ssa(
    ssa_blocks: &[SSABlock],
    stack_bases: BaseRegList,
) -> HashSet<String> {
    let mut pointer_vars: HashSet<String> = HashSet::new();
    let register_live_in_aliases = collect_register_live_in_aliases(ssa_blocks);
    let index_like_vars = infer_index_like_var_keys(ssa_blocks);
    let pointer_width = infer_pointer_width_bytes(ssa_blocks, stack_bases);
    let mut stack_addr_slots: HashMap<String, String> = HashMap::new();
    let mut pointer_stack_slots: HashSet<String> = HashSet::new();

    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::IntAdd { dst, a, b } | SSAOp::IntSub { dst, a, b } => {
                    let a_is_stack = ssa_var_is_stack_base(a, stack_bases);
                    let b_is_stack = ssa_var_is_stack_base(b, stack_bases);
                    let a_const = a.constant_bits();
                    let b_const = b.constant_bits();

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
                SSAOp::Load {
                    space: r2il::SpaceId::Ram,
                    addr,
                    ..
                }
                | SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr,
                    ..
                }
                | SSAOp::LoadLinked {
                    space: r2il::SpaceId::Ram,
                    addr,
                    ..
                }
                | SSAOp::StoreConditional {
                    space: r2il::SpaceId::Ram,
                    addr,
                    ..
                }
                | SSAOp::LoadGuarded {
                    space: r2il::SpaceId::Ram,
                    addr,
                    ..
                }
                | SSAOp::StoreGuarded {
                    space: r2il::SpaceId::Ram,
                    addr,
                    ..
                }
                | SSAOp::AtomicCAS {
                    space: r2il::SpaceId::Ram,
                    addr,
                    ..
                } => {
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
                    SSAOp::Store {
                        space: r2il::SpaceId::Ram,
                        addr,
                        val,
                    } => {
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
                    SSAOp::Load {
                        dst,
                        space: r2il::SpaceId::Ram,
                        addr,
                    } => {
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
        for (previous, live_in) in &register_live_in_aliases {
            if pointer_vars.contains(previous) {
                changed |= pointer_vars.insert(live_in.clone());
            }
            if pointer_vars.contains(live_in) {
                changed |= pointer_vars.insert(previous.clone());
            }
        }
    }

    pointer_vars
}

fn infer_pointer_pointee_width_bytes(
    ssa_blocks: &[SSABlock],
    pointer_vars: &HashSet<String>,
    stack_bases: BaseRegList,
) -> HashMap<String, u32> {
    let mut stack_addr_slots: HashMap<String, String> = HashMap::new();
    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::IntAdd { dst, a, b } => {
                    let (base, offset) = if ssa_var_is_stack_base(a, stack_bases) {
                        (a, b.constant_bits().map(|value| value as i64))
                    } else if ssa_var_is_stack_base(b, stack_bases) {
                        (b, a.constant_bits().map(|value| value as i64))
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
                SSAOp::IntSub { dst, a, b } if ssa_var_is_stack_base(a, stack_bases) => {
                    if let Some(offset) = b.constant_bits() {
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
                    let b_is_nonzero_const = b.constant_bits().is_some_and(|value| value != 0);
                    if !ssa_var_is_stack_base(a, stack_bases) && !b_is_nonzero_const {
                        add_pointer_pointee_flow_edge(&mut adjacency, pointer_vars, dst, a);
                    }
                    let a_is_nonzero_const = a.constant_bits().is_some_and(|value| value != 0);
                    if !ssa_var_is_stack_base(b, stack_bases)
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
                SSAOp::Load {
                    dst,
                    space: r2il::SpaceId::Ram,
                    addr,
                } => {
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
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr,
                    val,
                } => {
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
    arch_name: Option<&str>,
) -> (HashMap<String, TypeHint>, HashSet<String>) {
    let (_, stack_bases, _) = recover_vars_arch_profile(legacy_architecture_family(arch_name));
    let pointer_vars = infer_pointer_var_keys_from_ssa(ssa_blocks, stack_bases);
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

/// What the source calls the member at each offset of this function's
/// aggregates.
///
/// A binary that carried debug info already said what its struct fields are
/// called, and the access projections keep that beside the access that
/// reached them. Without it a field is named after its offset, so something
/// the source calls `next` prints as `f_10`.
///
/// The projections are read only under the identity they were sealed with,
/// and an offset two aggregates disagree about is dropped rather than
/// guessed.
pub fn source_field_names(prepared: &SsaArtifact) -> HashMap<u64, String> {
    let Some(interface) = prepared.machine_context().function_interface() else {
        return HashMap::new();
    };
    let Some(projections) = prepared
        .aggregate_accesses()
        .projections_for_revision(interface.revision_identity())
    else {
        return HashMap::new();
    };
    let mut names: HashMap<u64, String> = HashMap::new();
    let mut disputed = HashSet::new();
    for projection in projections.values() {
        if projection.member_name.is_empty() {
            continue;
        }
        match names.get(&projection.byte_offset) {
            Some(existing) if existing.as_str() != &*projection.member_name => {
                disputed.insert(projection.byte_offset);
            }
            Some(_) => {}
            None => {
                names.insert(projection.byte_offset, projection.member_name.to_string());
            }
        }
    }
    for offset in disputed {
        names.remove(&offset);
    }
    names
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prepared_aarch64_parameter(
        ops: Vec<r2il::R2ILOp>,
        declared_pointer: bool,
    ) -> r2ssa::SsaArtifact {
        let mut arch = r2il::ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(r2il::RegisterDef::new("x0", 0, 8));
        arch.add_register(r2il::RegisterDef::new("sp", 16, 8));
        arch.add_register(r2il::RegisterDef::new("lr", 24, 8));
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = if declared_pointer {
            let graph = r2ssa::SourceTypeGraph::new(
                [
                    r2ssa::SourceType::new(0, r2ssa::SourceTypeKind::UnsignedInteger, 8, 8),
                    r2ssa::SourceType::new(
                        1,
                        r2ssa::SourceTypeKind::Pointer { target_type_id: 0 },
                        64,
                        64,
                    ),
                ],
                [],
            )
            .expect("pointer type graph");
            r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
                b"prepare-source-pointer".to_vec(),
                "aarch64",
                [r2ssa::SourceAbiParameterSpec::new(0, storage(0))],
                r2ssa::SourceFunctionReturn::Void,
                [],
                [r2ssa::SourceLogicalValue::new(
                    1,
                    r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::Full, 0, 64),
                )],
                None,
                Some(graph),
            )
        } else {
            r2ssa::SourceFunctionInterface::new_exact(
                b"prepare-source-scalar".to_vec(),
                "aarch64",
                [r2ssa::SourceAbiParameterSpec::new(0, storage(0))],
                r2ssa::SourceFunctionReturn::Void,
                [],
            )
        }
        .and_then(|interface| interface.with_return_address_storage(storage(24)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(16)))
        .expect("exact AArch64 interface");
        let block = r2il::R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops,
            switch_info: None,
            op_metadata: Default::default(),
        };
        r2ssa::SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("prepared AArch64 parameter")
    }

    #[test]
    fn prepared_parameter_pointer_requires_use_or_exact_source_type() {
        let scalar = prepared_aarch64_parameter(
            vec![r2il::R2ILOp::IntLess {
                dst: r2il::Varnode::unique(0x10, 1),
                a: r2il::Varnode::register(0, 8),
                b: r2il::Varnode::constant(10, 8),
            }],
            false,
        );
        let dereferenced = prepared_aarch64_parameter(
            vec![r2il::R2ILOp::Load {
                dst: r2il::Varnode::unique(0x20, 1),
                space: r2il::SpaceId::Ram,
                addr: r2il::Varnode::register(0, 8),
            }],
            false,
        );
        let declared = prepared_aarch64_parameter(
            vec![r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(0x30, 8),
                src: r2il::Varnode::register(0, 8),
            }],
            true,
        );

        let initial_type = |prepared: &r2ssa::SsaArtifact| {
            recover_signature_params_from_prepared_ssa(prepared, 64)
                .into_iter()
                .find(|parameter| parameter.arg_index == 0)
                .expect("first parameter")
                .initial_ty
        };
        assert!(matches!(
            initial_type(&scalar),
            crate::CTypeLike::Int { .. }
        ));
        assert!(matches!(
            initial_type(&dereferenced),
            crate::CTypeLike::Pointer(_)
        ));
        assert!(matches!(
            initial_type(&declared),
            crate::CTypeLike::Pointer(_)
        ));
    }

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
    fn x86_argument_profile_is_selected_by_typed_machine_family() {
        let (x86_args, x86_stack, _) =
            recover_vars_arch_profile(r2ssa::MachineArchitectureFamily::X86);
        let (x86_64_args, x86_64_stack, _) =
            recover_vars_arch_profile(r2ssa::MachineArchitectureFamily::X86_64);

        assert!(x86_args.is_empty());
        assert_eq!(x86_stack, X86_STACK_BASES);
        assert_eq!(x86_64_args, X86_ARG_REGS);
        assert_eq!(x86_64_stack, X86_STACK_BASES);
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
    fn constant_spelling_cannot_authorize_stack_address_recovery() {
        let dst = SSAVar::new("tmp:address", 1, 8);
        let base = SSAVar::new("rsp", 0, 8);
        let spoofed = SSAOp::IntAdd {
            dst: dst.clone(),
            a: base.clone(),
            b: SSAVar::new("const:8", 0, 8),
        };
        let certified = SSAOp::IntAdd {
            dst,
            a: base.clone(),
            b: SSAVar::constant(8, 8),
        };

        assert!(!ssa_var_is_const(&SSAVar::new(
            "const:ffffffffffffffff",
            0,
            8
        )));
        assert!(stack_addr_temp(&spoofed, &["rsp"]).is_none());
        assert_eq!(
            stack_addr_temp(&certified, &["rsp"]),
            Some((certified.dst().expect("destination"), &base, 8))
        );
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
                signedness: crate::Signedness::Unknown,
            }
        );
    }

    #[test]
    fn recovered_signature_params_preserve_explicit_scalar_signedness() {
        let block = SSABlock {
            addr: 0x401000,
            size: 4,
            ops: vec![SSAOp::Copy {
                dst: SSAVar::new("tmp:0", 1, 8),
                src: SSAVar::new("rdi", 0, 8),
            }],
        };
        let hints = HashMap::from([(
            "rdi".to_string(),
            scalar_metadata_type_hint(MetadataScalarKind::UnsignedInt, 8)
                .expect("unsigned metadata hint"),
        )]);

        let params = recover_signature_params_from_ssa(&[block], Some("x86-64"), &hints, true, 64);

        assert_eq!(
            params[0].initial_ty,
            crate::CTypeLike::Int {
                bits: 64,
                signedness: crate::Signedness::Unsigned,
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
                    b: SSAVar::constant(0x38, 8),
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
                signedness: crate::Signedness::Unknown,
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
    fn x86_scalar_register_families_cover_legacy_and_extended_gprs() {
        let families: &[&[&str]] = &[
            &["RAX", "eax", "ax", "al", "ah"],
            &["RBX", "ebx", "bx", "bl", "bh"],
            &["RCX", "ecx", "cx", "cl", "ch"],
            &["RDX", "edx", "dx", "dl", "dh"],
            &["RSI", "esi", "si", "sil"],
            &["RDI", "edi", "di", "dil"],
            &["RBP", "ebp", "bp", "bpl"],
            &["RSP", "esp", "spl"],
            &["R8", "r8d", "r8w", "r8b"],
            &["R9", "r9d", "r9w", "r9b"],
            &["R10", "r10d", "r10w", "r10b"],
            &["R11", "r11d", "r11w", "r11b"],
            &["R12", "r12d", "r12w", "r12b"],
            &["R13", "r13d", "r13w", "r13b"],
            &["R14", "r14d", "r14w", "r14b"],
            &["R15", "r15d", "r15w", "r15b"],
        ];
        for aliases in families {
            let family = scalar_register_family_key(aliases[0]);
            for &alias in *aliases {
                assert_eq!(scalar_register_family_key(alias), family, "{alias}");
            }
        }
        assert_eq!(scalar_register_family_key("sp"), "aarch64:sp");
    }

    #[test]
    fn recovered_x86_second_arg_uses_low_32_carrier_width_in_either_op_order() {
        for narrow_first in [false, true] {
            let wide_use = SSAOp::IntAdd {
                dst: SSAVar::new("tmp:wide_sum", 1, 8),
                a: SSAVar::new("RSI", 0, 8),
                b: SSAVar::constant(7, 8),
            };
            let narrow_use = SSAOp::IntSub {
                dst: SSAVar::new("ESI", 1, 4),
                a: SSAVar::new("ESI", 0, 4),
                b: SSAVar::constant(3, 4),
            };
            let ops = if narrow_first {
                vec![narrow_use, wide_use]
            } else {
                vec![wide_use, narrow_use]
            };
            let block = SSABlock {
                addr: 0x401000,
                size: 8,
                ops,
            };

            let params = recover_signature_params_from_ssa(
                &[block],
                Some("x86-64"),
                &HashMap::new(),
                false,
                64,
            );
            let second = params
                .iter()
                .find(|param| param.arg_index == 1)
                .expect("second ABI parameter");
            assert_eq!(second.name, "arg1");
            assert_eq!(
                second.initial_ty,
                crate::CTypeLike::Int {
                    bits: 32,
                    signedness: crate::Signedness::Unknown,
                },
                "narrow_first={narrow_first}"
            );
        }
    }

    #[test]
    fn recovered_x86_pointer_carrier_stays_pointer_despite_low_alias_use() {
        let block = SSABlock {
            addr: 0x401000,
            size: 12,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:address", 1, 8),
                    a: SSAVar::new("RDI", 0, 8),
                    b: SSAVar::constant(4, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:value", 1, 4),
                    addr: SSAVar::new("tmp:address", 1, 8),
                    space: r2il::SpaceId::Ram,
                },
                SSAOp::IntSub {
                    dst: SSAVar::new("EDI", 1, 4),
                    a: SSAVar::new("EDI", 0, 4),
                    b: SSAVar::constant(1, 4),
                },
            ],
        };

        let params =
            recover_signature_params_from_ssa(&[block], Some("x86-64"), &HashMap::new(), false, 64);
        let first = params
            .iter()
            .find(|param| param.arg_index == 0)
            .expect("first ABI parameter");
        assert_eq!(first.ssa_var, SSAVar::new("RDI", 0, 8));
        assert!(matches!(first.initial_ty, crate::CTypeLike::Pointer(_)));
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
                    b: SSAVar::constant(8, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:stack_arg", 1, 8),
                    addr: SSAVar::new("tmp:sp8", 1, 8),
                    space: r2il::SpaceId::Ram,
                },
            ],
        };

        let params =
            recover_signature_params_from_ssa(&[block], Some("x86-64"), &HashMap::new(), true, 64);

        assert_eq!(params.len(), 2);
        assert_eq!(params[0].name, "arg0");
        assert_eq!(params[0].arg_index, 0);
        assert_eq!(params[0].ssa_var, SSAVar::new("rdi", 0, 8));
        assert_eq!(params[1].name, "arg6");
        assert_eq!(params[1].arg_index, 6);
        assert_eq!(params[1].ssa_var, SSAVar::new("tmp:stack_arg", 1, 8));
        assert_eq!(
            params[1].initial_ty,
            crate::CTypeLike::Int {
                bits: 64,
                signedness: crate::Signedness::Unknown,
            }
        );
    }

    #[test]
    fn only_ram_accesses_recover_stack_params_and_locals() {
        let block_for_space = |space| SSABlock {
            addr: 0x401000,
            size: 16,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:incoming", 1, 8),
                    a: SSAVar::new("rsp", 0, 8),
                    b: SSAVar::constant(8, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:stack_arg", 1, 8),
                    space,
                    addr: SSAVar::new("tmp:incoming", 1, 8),
                },
                SSAOp::IntSub {
                    dst: SSAVar::new("tmp:local", 1, 8),
                    a: SSAVar::new("rbp", 1, 8),
                    b: SSAVar::constant(8, 8),
                },
                SSAOp::Store {
                    space,
                    addr: SSAVar::new("tmp:local", 1, 8),
                    val: SSAVar::new("tmp:value", 1, 4),
                },
            ],
        };

        let ram = block_for_space(r2il::SpaceId::Ram);
        let custom = block_for_space(r2il::SpaceId::Custom(7));
        let ram_params = recover_signature_params_from_ssa(
            std::slice::from_ref(&ram),
            Some("x86-64"),
            &HashMap::new(),
            true,
            64,
        );
        let custom_params = recover_signature_params_from_ssa(
            std::slice::from_ref(&custom),
            Some("x86-64"),
            &HashMap::new(),
            true,
            64,
        );
        assert!(ram_params.iter().any(|param| param.arg_index == 6));
        assert!(!custom_params.iter().any(|param| param.arg_index == 6));

        let ram_vars = recover_vars_from_ssa(&[ram], Some("x86-64"), &HashMap::new(), true);
        let custom_vars = recover_vars_from_ssa(&[custom], Some("x86-64"), &HashMap::new(), true);
        assert!(ram_vars.iter().any(|var| var.kind == "s" && var.delta == 8));
        assert!(
            ram_vars
                .iter()
                .any(|var| var.kind == "b" && var.delta == -8)
        );
        assert!(
            !custom_vars
                .iter()
                .any(|var| matches!(var.kind.as_str(), "s" | "b"))
        );
    }

    #[test]
    fn custom_stack_home_does_not_create_abi_pointer_evidence() {
        let blocks_for_space = |space| {
            vec![SSABlock {
                addr: 0x401000,
                size: 16,
                ops: vec![
                    SSAOp::IntSub {
                        dst: SSAVar::new("tmp:home", 1, 8),
                        a: SSAVar::new("rbp", 1, 8),
                        b: SSAVar::constant(8, 8),
                    },
                    SSAOp::Copy {
                        dst: SSAVar::new("tmp:saved_arg", 1, 8),
                        src: SSAVar::new("rdi", 0, 8),
                    },
                    SSAOp::Store {
                        space,
                        addr: SSAVar::new("tmp:home", 1, 8),
                        val: SSAVar::new("tmp:saved_arg", 1, 8),
                    },
                    SSAOp::Load {
                        dst: SSAVar::new("tmp:base", 1, 8),
                        space,
                        addr: SSAVar::new("tmp:home", 1, 8),
                    },
                    SSAOp::Load {
                        dst: SSAVar::new("tmp:value", 1, 4),
                        space,
                        addr: SSAVar::new("tmp:base", 1, 8),
                    },
                ],
            }]
        };
        let param_type_for_space = |space| {
            recover_signature_params_from_ssa(
                &blocks_for_space(space),
                Some("x86-64"),
                &HashMap::new(),
                false,
                64,
            )
            .into_iter()
            .find(|param| param.arg_index == 0)
            .expect("rdi parameter")
            .initial_ty
        };

        assert!(matches!(
            param_type_for_space(r2il::SpaceId::Ram),
            crate::CTypeLike::Pointer(_)
        ));
        assert!(matches!(
            param_type_for_space(r2il::SpaceId::Custom(7)),
            crate::CTypeLike::Int { .. }
        ));
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
                    b: SSAVar::constant(0xffff_ffff_ffff_fff8, 8),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("tmp:saved_arg", 1, 8),
                    src: SSAVar::new("rdi", 0, 8),
                },
                SSAOp::Store {
                    addr: SSAVar::new("tmp:home", 1, 8),
                    val: SSAVar::new("tmp:saved_arg", 1, 8),
                    space: r2il::SpaceId::Ram,
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
                    b: SSAVar::constant(0xffff_ffff_ffff_fff8, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:base", 1, 8),
                    addr: SSAVar::new("tmp:home_reload", 1, 8),
                    space: r2il::SpaceId::Ram,
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
                    b: SSAVar::constant(4, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:element", 1, 8),
                    a: SSAVar::new("rax", 3, 8),
                    b: SSAVar::new("tmp:scaled", 1, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:value", 1, 4),
                    addr: SSAVar::new("tmp:element", 1, 8),
                    space: r2il::SpaceId::Ram,
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
            arg0.initial_ty,
            crate::CTypeLike::Pointer(Box::new(crate::CTypeLike::Int {
                bits: 32,
                signedness: crate::Signedness::Unknown,
            }))
        );
    }

    #[test]
    fn pointer_evidence_does_not_cross_unrelated_register_versions() {
        let block = SSABlock {
            addr: 0x1000,
            size: 16,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 1, 8),
                    a: SSAVar::new("sp", 1, 8),
                    b: SSAVar::constant(16, 8),
                },
                SSAOp::Store {
                    addr: SSAVar::new("tmp:slot", 1, 8),
                    val: SSAVar::new("x1", 0, 8),
                    space: r2il::SpaceId::Ram,
                },
                SSAOp::Load {
                    dst: SSAVar::new("x9", 1, 8),
                    addr: SSAVar::new("tmp:slot", 1, 8),
                    space: r2il::SpaceId::Ram,
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:value", 1, 1),
                    addr: SSAVar::new("x9", 2, 8),
                    space: r2il::SpaceId::Ram,
                },
            ],
        };

        let evidence = collect_signature_type_evidence_context_with_arch(&[block], Some("aarch64"));

        assert!(
            evidence
                .pointer_vars
                .contains(&ssa_var_key(&SSAVar::new("X9", 2, 8)))
        );
        assert!(
            !evidence
                .pointer_vars
                .contains(&ssa_var_key(&SSAVar::new("X9", 1, 8)))
        );
        assert!(
            !evidence
                .pointer_vars
                .contains(&ssa_var_key(&SSAVar::new("X1", 0, 8)))
        );
    }

    #[test]
    fn copied_constant_scale_preserves_parameter_pointer_identity() {
        let block = SSABlock {
            addr: 0x1000,
            size: 16,
            ops: vec![
                SSAOp::IntSExt {
                    dst: SSAVar::new("x9", 1, 8),
                    src: SSAVar::new("w1", 0, 4),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("x10", 1, 8),
                    src: SSAVar::constant(40, 8),
                },
                SSAOp::IntMult {
                    dst: SSAVar::new("x9", 2, 8),
                    a: SSAVar::new("x9", 1, 8),
                    b: SSAVar::new("x10", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:element", 1, 8),
                    a: SSAVar::new("x0", 0, 8),
                    b: SSAVar::new("x9", 2, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:value", 1, 4),
                    addr: SSAVar::new("tmp:element", 1, 8),
                    space: r2il::SpaceId::Ram,
                },
            ],
        };

        let evidence = collect_signature_type_evidence_context_with_arch(&[block], Some("aarch64"));

        assert!(
            evidence
                .pointer_vars
                .contains(&ssa_var_key(&SSAVar::new("X0", 0, 8)))
        );
        assert_eq!(
            evidence
                .pointer_pointee_width_bytes
                .get(&ssa_var_key(&SSAVar::new("X0", 0, 8))),
            Some(&4)
        );
    }

    #[test]
    fn arm64_pointer_pointee_width_flows_through_stack_home_and_shifted_index() {
        let home = SSAVar::new("tmp:home", 1, 8);
        let reload = SSAVar::new("tmp:reload", 1, 8);
        let base = SSAVar::new("x8", 4, 8);
        let index = SSAVar::new("tmp:index", 1, 4);
        let wide_index = SSAVar::new("x9", 3, 8);
        let scaled = SSAVar::new("tmp:scaled", 1, 8);
        let element = SSAVar::new("tmp:element", 1, 8);
        let entry = SSABlock {
            addr: 0x1000,
            size: 8,
            ops: vec![
                SSAOp::IntAdd {
                    dst: home.clone(),
                    a: SSAVar::new("sp", 1, 8),
                    b: SSAVar::constant(24, 8),
                },
                SSAOp::Store {
                    addr: home,
                    val: SSAVar::new("x0", 0, 8),
                    space: r2il::SpaceId::Ram,
                },
            ],
        };
        let body = SSABlock {
            addr: 0x1010,
            size: 20,
            ops: vec![
                SSAOp::IntAdd {
                    dst: reload.clone(),
                    a: SSAVar::new("sp", 1, 8),
                    b: SSAVar::constant(24, 8),
                },
                SSAOp::Load {
                    dst: base.clone(),
                    addr: reload,
                    space: r2il::SpaceId::Ram,
                },
                SSAOp::IntSExt {
                    dst: wide_index.clone(),
                    src: index,
                },
                SSAOp::IntLeft {
                    dst: scaled.clone(),
                    a: wide_index,
                    b: SSAVar::constant(2, 8),
                },
                SSAOp::IntAdd {
                    dst: element.clone(),
                    a: base,
                    b: scaled,
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:value", 1, 4),
                    addr: element,
                    space: r2il::SpaceId::Ram,
                },
            ],
        };

        let evidence =
            collect_signature_type_evidence_context_with_arch(&[entry, body], Some("aarch64"));
        assert!(
            evidence
                .pointer_vars
                .contains(&ssa_var_key(&SSAVar::new("X0", 0, 8)))
        );
        assert_eq!(
            evidence
                .pointer_pointee_width_bytes
                .get(&ssa_var_key(&SSAVar::new("X0", 0, 8))),
            Some(&4),
            "pointer_vars={:?} pointee_widths={:?}",
            evidence.pointer_vars,
            evidence.pointer_pointee_width_bytes
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
                    b: SSAVar::constant(8, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:stack_arg", 1, 8),
                    addr: SSAVar::new("tmp:sp8", 1, 8),
                    space: r2il::SpaceId::Ram,
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
    fn prepared_stack_roots_recover_entry_relative_arm64_locals() {
        let slot_addr = SSAVar::new("tmp:slot", 1, 8);
        let block = SSABlock {
            addr: 0x1000,
            size: 8,
            ops: vec![
                SSAOp::IntAdd {
                    dst: slot_addr.clone(),
                    a: SSAVar::new("sp", 1, 8),
                    b: SSAVar::constant(12, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: slot_addr.clone(),
                    val: SSAVar::constant(1, 4),
                },
            ],
        };
        let prep_facts = DecompilePrepFacts {
            stack_address_roots: [(
                slot_addr,
                r2ssa::StackAddressRoot {
                    base: StackAddressBase::StackPointer,
                    offset: -4,
                },
            )]
            .into_iter()
            .collect(),
            ..DecompilePrepFacts::default()
        };

        let vars = recover_vars_from_ssa_with_prep_facts(
            &[block],
            Some(&prep_facts),
            Some("aarch64"),
            &HashMap::new(),
            true,
        );
        let local = vars
            .iter()
            .find(|var| var.kind == "s")
            .expect("canonical stack local");

        assert_eq!(local.delta, -4);
        assert_eq!(local.name, "var_4h");
        assert!(!local.isarg);
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
                    b: SSAVar::constant(8, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("rip", 1, 8),
                    addr: SSAVar::new("rsp", 2, 8),
                    space: r2il::SpaceId::Ram,
                },
                SSAOp::Return {
                    target: SSAVar::new("rip", 1, 8),
                },
            ],
        };

        let vars = recover_vars_from_ssa(&[block], Some("x86-64"), &HashMap::new(), true);

        assert!(vars.iter().all(|var| !var.isarg));
        assert!(vars.iter().all(|var| var.delta != 8));
    }

    #[test]
    fn recover_vars_from_ssa_rejects_constant_minus_stack_pointer_as_an_address() {
        let block = SSABlock {
            addr: 0x401000,
            size: 8,
            ops: vec![
                SSAOp::IntSub {
                    dst: SSAVar::new("tmp:not_stack", 1, 8),
                    a: SSAVar::constant(0x20, 8),
                    b: SSAVar::new("rsp", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:value", 1, 8),
                    addr: SSAVar::new("tmp:not_stack", 1, 8),
                    space: r2il::SpaceId::Ram,
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
