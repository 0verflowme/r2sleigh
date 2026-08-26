use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use r2ssa::{ObjectKind, SSAFunction, SSAOp, SSAVar, SsaArtifact};

use crate::convert::CTypeLike;
use crate::facts::{FunctionSignatureSpec, FunctionType, signature_strength};
use crate::inference::TypeInference;
use crate::model::Signedness;
use crate::prepare::{
    SignatureTypeEvidenceContext, prepared_arch_name, recover_signature_params_from_prepared_ssa,
    scalar_register_family_key, ssa_var_is_register_like,
};
use crate::signature::SignatureRegistry;
use crate::signedness::{ScalarSignednessEvidence, infer_scalar_signedness};
use crate::writeback::{InferredSignature, InferredSignatureParam};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SignatureTypeEvidence {
    pub pointer_proven: u8,
    pub pointer_likely: u8,
    pub scalar_proven: u8,
    pub scalar_likely: u8,
    pub bool_like: u8,
    pub width_bits: u32,
}

impl SignatureTypeEvidence {
    pub fn pointer_score(&self) -> u16 {
        (self.pointer_proven as u16) * 4 + (self.pointer_likely as u16) * 2
    }

    pub fn scalar_score(&self) -> u16 {
        (self.scalar_proven as u16) * 4
            + (self.scalar_likely as u16) * 2
            + (self.bool_like as u16) * 3
    }

    pub fn has_pointer_signal(&self) -> bool {
        self.pointer_proven > 0 || self.pointer_likely > 0
    }

    pub fn has_scalar_signal(&self) -> bool {
        self.scalar_proven > 0 || self.scalar_likely > 0 || self.bool_like > 0
    }

    pub fn has_conflict(&self) -> bool {
        self.has_pointer_signal() && self.has_scalar_signal()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureParamCandidate {
    pub name: String,
    pub ty: CTypeLike,
    pub arg_index: usize,
    pub size_bytes: u32,
    pub evidence: SignatureTypeEvidence,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoveredSignatureParam {
    pub name: String,
    pub arg_index: usize,
    pub ssa_var: SSAVar,
    pub initial_ty: CTypeLike,
}

pub fn infer_signature_from_prepared_ssa(prepared: &SsaArtifact) -> InferredSignature {
    let function_name = prepared
        .function()
        .name
        .clone()
        .unwrap_or_else(|| format!("fcn.{:x}", prepared.function().entry));
    let ptr_bits = prepared
        .machine_context()
        .memory_model()
        .default_address_bits();
    let recovered_params = recover_signature_params_from_prepared_ssa(prepared, ptr_bits);
    let arch_name = prepared_arch_name(prepared).unwrap_or("");
    let evidence_types = crate::solve_evidence_types(prepared, &BTreeMap::new(), ptr_bits);
    let certified_parameter_widths = certified_parameter_memory_widths(prepared);

    let mut canonical_params = recovered_params
        .iter()
        .map(|param| {
            let certified_ty = certified_parameter_pointer_type(
                param.initial_ty.clone(),
                certified_parameter_widths.get(&param.arg_index),
            );
            let initial_ty = prepared
                .graph()
                .value_id_for_var(&param.ssa_var)
                .and_then(|value| evidence_types.value_type(value))
                .cloned()
                .unwrap_or(certified_ty);
            let mut evidence = exact_signature_type_evidence(&initial_ty);
            if certified_parameter_widths.contains_key(&param.arg_index) {
                evidence.pointer_proven = evidence.pointer_proven.max(1);
            }
            let ty = resolve_evidence_driven_signature_type(
                initial_ty,
                param.ssa_var.size,
                ptr_bits,
                &evidence,
            );
            SignatureParamCandidate {
                name: param.name.clone(),
                ty,
                arg_index: param.arg_index,
                size_bytes: param.ssa_var.size,
                evidence,
            }
        })
        .collect::<Vec<_>>();

    for param in &mut canonical_params {
        param.ty = resolve_evidence_driven_signature_type(
            param.ty.clone(),
            param.size_bytes,
            ptr_bits,
            &param.evidence,
        );
    }
    refine_parameter_signedness(
        arch_name,
        prepared,
        &recovered_params,
        &mut canonical_params,
    );

    let (ret_type, ret_evidence) =
        infer_signature_return_type_from_prepared(prepared, &evidence_types, ptr_bits);
    let mut inferred = build_inferred_signature(
        &function_name,
        arch_name,
        ptr_bits,
        &canonical_params,
        &ret_type,
        &ret_evidence,
        &HashMap::new(),
    );
    if let Some(interface) = prepared.machine_context().function_interface() {
        inferred.callconv = interface.calling_convention().to_string();
        inferred.callconv_confidence = 100;
    } else {
        inferred.callconv = "unknown".to_string();
        inferred.callconv_confidence = 0;
    }
    inferred
}

fn certified_parameter_memory_widths(prepared: &SsaArtifact) -> HashMap<usize, BTreeSet<u32>> {
    let mut widths = HashMap::<usize, BTreeSet<u32>>::new();
    for access in prepared.certificates().memory_accesses.values() {
        let Some(index) = certified_memory_parameter(prepared, access) else {
            continue;
        };
        widths.entry(index).or_default().insert(access.width);
    }
    widths
}

fn certified_memory_parameter(
    prepared: &SsaArtifact,
    access: &r2ssa::MemoryAccessCertificate,
) -> Option<usize> {
    if access.space != r2il::SpaceId::Ram
        || prepared
            .machine_context()
            .memory_space_at(access.block_addr, access.op_index)
            != Some(access.space)
    {
        return None;
    }
    prepared
        .objects()
        .object(access.object)
        .and_then(|object| match object.kind {
            ObjectKind::Parameter {
                space: r2il::SpaceId::Ram,
                index,
            } => Some(index),
            _ => None,
        })
        .or_else(|| {
            prepared
                .addresses()
                .parameter_expression(access.address)
                .map(|expression| expression.parameter)
        })
}

fn certified_parameter_pointer_type(
    initial_ty: CTypeLike,
    widths: Option<&BTreeSet<u32>>,
) -> CTypeLike {
    let Some(widths) = widths else {
        return initial_ty;
    };
    if matches!(
        initial_ty,
        CTypeLike::Pointer(ref inner)
            if !matches!(inner.as_ref(), CTypeLike::Void | CTypeLike::Unknown)
    ) {
        return initial_ty;
    }
    let Some(width) = widths.first().copied().filter(|_| widths.len() == 1) else {
        return CTypeLike::Pointer(Box::new(CTypeLike::Void));
    };
    let bits = width.saturating_mul(8);
    if !matches!(bits, 8 | 16 | 32 | 64) {
        return CTypeLike::Pointer(Box::new(CTypeLike::Void));
    }
    CTypeLike::Pointer(Box::new(CTypeLike::Int {
        bits,
        signedness: Signedness::Unknown,
    }))
}

fn refine_parameter_signedness(
    arch_name: &str,
    prepared: &SsaArtifact,
    recovered_params: &[RecoveredSignatureParam],
    params: &mut [SignatureParamCandidate],
) {
    let parameter_home_aliases = certified_parameter_home_aliases(prepared, recovered_params);
    let inferred = infer_scalar_signedness(
        prepared
            .function()
            .blocks()
            .flat_map(|block| block.ops.iter()),
        prepared
            .function()
            .blocks()
            .flat_map(|block| {
                block
                    .phis
                    .iter()
                    .flat_map(|phi| phi.sources.iter().map(|(_, source)| (source, &phi.dst)))
            })
            .chain(
                prepared
                    .certificates()
                    .stack_reloads
                    .values()
                    .filter_map(|reload| {
                        if reload.value_width != reload.memory_width {
                            return None;
                        }
                        Some((
                            prepared.value_var(reload.canonical_source)?,
                            prepared.value_var(reload.value)?,
                        ))
                    }),
            )
            .chain(
                parameter_home_aliases
                    .iter()
                    .map(|(source, reload)| (source, reload)),
            ),
        (!arch_name.is_empty()).then_some(arch_name),
    );
    let mut pointee_evidence = HashMap::<(usize, u32), BTreeSet<ScalarSignednessEvidence>>::new();
    for access in prepared.certificates().memory_accesses.values() {
        let Some(index) = certified_memory_parameter(prepared, access) else {
            continue;
        };
        let Some(value) = access.value.and_then(|value| prepared.value_var(value)) else {
            continue;
        };
        if value.size != access.width {
            continue;
        }
        let Some(observed) = inferred.get(value) else {
            continue;
        };
        pointee_evidence
            .entry((index, access.width.saturating_mul(8)))
            .or_default()
            .extend(observed.iter().copied());
    }

    for param in params {
        let scalar_observed = recovered_params
            .iter()
            .find(|recovered| recovered.arg_index == param.arg_index)
            .and_then(|recovered| inferred.get(&recovered.ssa_var));
        let observed = match &mut param.ty {
            CTypeLike::Int { signedness, .. } if *signedness == Signedness::Unknown => {
                scalar_observed
            }
            CTypeLike::Pointer(inner) => match inner.as_mut() {
                CTypeLike::Int { bits, signedness } if *signedness == Signedness::Unknown => {
                    pointee_evidence.get(&(param.arg_index, *bits))
                }
                _ => None,
            },
            _ => None,
        };
        let Some(signedness) = singleton_signedness(observed) else {
            continue;
        };
        match &mut param.ty {
            CTypeLike::Int {
                signedness: target, ..
            } => *target = signedness,
            CTypeLike::Pointer(inner) => {
                if let CTypeLike::Int {
                    signedness: target, ..
                } = inner.as_mut()
                {
                    *target = signedness;
                }
            }
            _ => {}
        }
    }
}

fn certified_parameter_home_aliases(
    prepared: &SsaArtifact,
    recovered_params: &[RecoveredSignatureParam],
) -> Vec<(SSAVar, SSAVar)> {
    let mut writes = HashMap::<r2ssa::ObjectId, Vec<&r2ssa::MemoryAccessCertificate>>::new();
    for access in prepared.certificates().memory_accesses.values() {
        if access.is_write
            && access.space == r2il::SpaceId::Ram
            && prepared
                .objects()
                .object(access.object)
                .is_some_and(|object| {
                    matches!(
                        object.kind,
                        ObjectKind::StackSlot {
                            space: r2il::SpaceId::Ram,
                            ..
                        } | ObjectKind::FrameObject {
                            space: r2il::SpaceId::Ram,
                            ..
                        }
                    )
                })
        {
            writes.entry(access.object).or_default().push(access);
        }
    }

    let mut aliases = Vec::new();
    for (object, stores) in writes {
        let [store] = stores.as_slice() else {
            continue;
        };
        let Some(stored) = store
            .value
            .and_then(|value| transparent_same_width_source(prepared, value))
        else {
            continue;
        };
        let Some(parameter) = recovered_params
            .iter()
            .find(|parameter| parameter.ssa_var == stored)
        else {
            continue;
        };
        for load in prepared
            .certificates()
            .memory_accesses
            .values()
            .filter(|access| {
                !access.is_write && access.space == r2il::SpaceId::Ram && access.object == object
            })
        {
            if load.width != store.width || load.width != parameter.ssa_var.size {
                continue;
            }
            let Some(reload) = load
                .value
                .and_then(|value| prepared.value_var(value))
                .cloned()
            else {
                continue;
            };
            aliases.push((parameter.ssa_var.clone(), reload));
        }
    }
    aliases.sort();
    aliases.dedup();
    aliases
}

fn transparent_same_width_source(prepared: &SsaArtifact, start: r2ssa::ValueId) -> Option<SSAVar> {
    let mut current = start;
    let mut visited = HashSet::new();
    while visited.insert(current) {
        let current_var = prepared.value_var(current)?.clone();
        let Some(inst) = prepared
            .graph()
            .def_inst(current)
            .and_then(|inst| prepared.graph().inst(inst))
        else {
            return Some(current_var);
        };
        let r2ssa::InstPayload::Op(op) = &inst.payload else {
            return Some(current_var);
        };
        let source = match op {
            SSAOp::Copy { src, .. } | SSAOp::New { src, .. } | SSAOp::Cast { src, .. } => src,
            SSAOp::Subpiece { src, offset, .. } if *offset == 0 && src.size == current_var.size => {
                src
            }
            _ => return Some(current_var),
        };
        if source.size != current_var.size {
            return Some(current_var);
        }
        let Some(source_value) = prepared.graph().value_id_for_var(source) else {
            return Some(current_var);
        };
        current = source_value;
    }
    None
}

fn singleton_signedness(
    observed: Option<&BTreeSet<ScalarSignednessEvidence>>,
) -> Option<Signedness> {
    let observed = observed?.iter();
    if observed.len() != 1 {
        return None;
    }
    match observed.copied().next()? {
        ScalarSignednessEvidence::Signed => Some(Signedness::Signed),
        ScalarSignednessEvidence::Unsigned => Some(Signedness::Unsigned),
    }
}

pub fn merge_initial_signature_type_evidence(
    initial_ty: &CTypeLike,
    evidence: &mut SignatureTypeEvidence,
) {
    match initial_ty {
        CTypeLike::Pointer(_) => evidence.pointer_likely = evidence.pointer_likely.max(1),
        CTypeLike::Bool => evidence.bool_like = evidence.bool_like.max(1),
        CTypeLike::Int { bits, .. } => {
            evidence.scalar_likely = evidence.scalar_likely.max(1);
            if !(evidence.has_scalar_signal()
                && !evidence.has_pointer_signal()
                && evidence.width_bits > 0
                && evidence.width_bits < *bits)
            {
                evidence.width_bits = evidence.width_bits.max(*bits);
            }
        }
        CTypeLike::Float(bits) => {
            evidence.scalar_proven = evidence.scalar_proven.max(1);
            evidence.width_bits = evidence.width_bits.max(*bits);
        }
        _ => {}
    }
}

fn fallback_scalar_type_like(
    var_size_bytes: u32,
    evidence: &SignatureTypeEvidence,
    ptr_bits: u32,
) -> CTypeLike {
    if evidence.bool_like > 0
        && evidence.pointer_score() == 0
        && evidence.scalar_proven == 0
        && evidence.scalar_likely <= 1
    {
        return CTypeLike::Bool;
    }

    let carrier_bits = var_size_bytes.saturating_mul(8);
    let width_bits = if evidence.has_scalar_signal()
        && !evidence.has_pointer_signal()
        && evidence.width_bits > 0
    {
        evidence.width_bits
    } else {
        evidence.width_bits.max(carrier_bits)
    };
    let width_bits = match width_bits {
        0 => {
            if ptr_bits >= 64 {
                64
            } else {
                32
            }
        }
        1 => 8,
        2..=8 => 8,
        9..=16 => 16,
        17..=32 => 32,
        _ => 64,
    };

    CTypeLike::Int {
        bits: width_bits,
        signedness: Signedness::Signed,
    }
}

fn is_unmaterialized_aggregate_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower.is_empty() || lower == "anon" || lower.starts_with("anon_")
}

pub fn materialize_signature_type_like(ty: CTypeLike, ptr_bits: u32) -> CTypeLike {
    match ty {
        CTypeLike::Pointer(inner) => {
            if matches!(*inner, CTypeLike::Unknown | CTypeLike::Void)
                || matches!(
                    inner.as_ref(),
                    CTypeLike::Struct(name)
                        | CTypeLike::Union(name)
                        | CTypeLike::Enum(name)
                        if is_unmaterialized_aggregate_name(name)
                )
            {
                return CTypeLike::Pointer(Box::new(CTypeLike::Void));
            }
            CTypeLike::Pointer(Box::new(materialize_signature_type_like(*inner, ptr_bits)))
        }
        CTypeLike::Array(inner, len) => {
            if matches!(*inner, CTypeLike::Unknown | CTypeLike::Void) {
                return CTypeLike::Array(
                    Box::new(CTypeLike::Int {
                        bits: 8,
                        signedness: Signedness::Unsigned,
                    }),
                    len,
                );
            }
            CTypeLike::Array(
                Box::new(materialize_signature_type_like(*inner, ptr_bits)),
                len,
            )
        }
        CTypeLike::Unknown => {
            fallback_scalar_type_like((ptr_bits / 8).max(1), &Default::default(), ptr_bits)
        }
        CTypeLike::Struct(name) if is_unmaterialized_aggregate_name(&name) => {
            fallback_scalar_type_like((ptr_bits / 8).max(1), &Default::default(), ptr_bits)
        }
        CTypeLike::Union(name) if is_unmaterialized_aggregate_name(&name) => {
            fallback_scalar_type_like((ptr_bits / 8).max(1), &Default::default(), ptr_bits)
        }
        CTypeLike::Enum(name) if is_unmaterialized_aggregate_name(&name) => {
            fallback_scalar_type_like((ptr_bits / 8).max(1), &Default::default(), ptr_bits)
        }
        CTypeLike::Typedef(name) if name.trim().is_empty() => {
            fallback_scalar_type_like((ptr_bits / 8).max(1), &Default::default(), ptr_bits)
        }
        other => other,
    }
}

pub fn render_signature_type(ty: &CTypeLike, ptr_bits: u32) -> String {
    match materialize_signature_type_like(ty.clone(), ptr_bits) {
        CTypeLike::Void => "void".to_string(),
        CTypeLike::Bool => "bool".to_string(),
        CTypeLike::Int {
            bits: 8,
            signedness: Signedness::Signed,
        } => "int8_t".to_string(),
        CTypeLike::Int {
            bits: 16,
            signedness: Signedness::Signed,
        } => "int16_t".to_string(),
        CTypeLike::Int {
            bits: 32,
            signedness: Signedness::Signed,
        } => "int32_t".to_string(),
        CTypeLike::Int {
            bits: 64,
            signedness: Signedness::Signed,
        } => "int64_t".to_string(),
        CTypeLike::Int {
            bits,
            signedness: Signedness::Signed | Signedness::Unknown,
        } => format!("int{bits}_t"),
        CTypeLike::Int {
            bits: 8,
            signedness: Signedness::Unsigned,
        } => "uint8_t".to_string(),
        CTypeLike::Int {
            bits: 16,
            signedness: Signedness::Unsigned,
        } => "uint16_t".to_string(),
        CTypeLike::Int {
            bits: 32,
            signedness: Signedness::Unsigned,
        } => "uint32_t".to_string(),
        CTypeLike::Int {
            bits: 64,
            signedness: Signedness::Unsigned,
        } => "uint64_t".to_string(),
        CTypeLike::Int {
            bits,
            signedness: Signedness::Unsigned,
        } => format!("uint{bits}_t"),
        CTypeLike::Float(32) => "float".to_string(),
        CTypeLike::Float(64) => "double".to_string(),
        CTypeLike::Float(bits) => format!("float{bits}"),
        CTypeLike::Pointer(inner) => format!("{}*", render_signature_type(&inner, ptr_bits)),
        CTypeLike::Array(inner, Some(size)) => {
            format!("{}[{}]", render_signature_type(&inner, ptr_bits), size)
        }
        CTypeLike::Array(inner, None) => format!("{}[]", render_signature_type(&inner, ptr_bits)),
        CTypeLike::Struct(name) => format!("struct {name}"),
        CTypeLike::Union(name) => format!("union {name}"),
        CTypeLike::Enum(name) => format!("enum {name}"),
        CTypeLike::Typedef(name) => name,
        CTypeLike::Function => "void (*)()".to_string(),
        CTypeLike::Unknown => "int64_t".to_string(),
    }
}

fn sanitize_signature_type_like(
    mut ty: CTypeLike,
    var_size_bytes: u32,
    ptr_bits: u32,
) -> CTypeLike {
    if matches!(ty, CTypeLike::Void | CTypeLike::Unknown) {
        ty = match var_size_bytes {
            1 => CTypeLike::Int {
                bits: 8,
                signedness: Signedness::Signed,
            },
            2 => CTypeLike::Int {
                bits: 16,
                signedness: Signedness::Signed,
            },
            4 => CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            },
            8 => CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed,
            },
            _ => CTypeLike::Unknown,
        };
    }

    if matches!(ty, CTypeLike::Void | CTypeLike::Unknown) {
        ty = CTypeLike::Int {
            bits: if ptr_bits >= 64 { 64 } else { 32 },
            signedness: Signedness::Signed,
        };
    }

    ty
}

pub fn resolve_evidence_driven_signature_type(
    initial_ty: CTypeLike,
    var_size_bytes: u32,
    ptr_bits: u32,
    evidence: &SignatureTypeEvidence,
) -> CTypeLike {
    if matches!(initial_ty, CTypeLike::Float(_)) {
        return initial_ty;
    }

    let pointer_score = evidence.pointer_score();
    let scalar_score = evidence.scalar_score();
    let initial_is_pointer = matches!(initial_ty, CTypeLike::Pointer(_));
    let initial_is_scalar = matches!(initial_ty, CTypeLike::Bool | CTypeLike::Int { .. });
    let preferred_scalar = fallback_scalar_type_like(var_size_bytes, evidence, ptr_bits);
    let scalar_width_narrows = match (&initial_ty, &preferred_scalar) {
        (
            CTypeLike::Int {
                bits: initial_bits, ..
            },
            CTypeLike::Int {
                bits: preferred_bits,
                ..
            },
        ) => preferred_bits < initial_bits,
        (CTypeLike::Int { .. }, CTypeLike::Bool) => true,
        _ => false,
    };

    if initial_is_pointer && pointer_score.saturating_add(1) >= scalar_score {
        return initial_ty;
    }
    if initial_is_scalar && scalar_score.saturating_add(1) >= pointer_score {
        if scalar_width_narrows
            && evidence.has_scalar_signal()
            && !evidence.has_pointer_signal()
            && !evidence.has_conflict()
        {
            return preferred_scalar;
        }
        return initial_ty;
    }

    match initial_ty {
        CTypeLike::Struct(_) | CTypeLike::Union(_) | CTypeLike::Enum(_) | CTypeLike::Typedef(_) => {
            if pointer_score > scalar_score.saturating_add(1) {
                return CTypeLike::Pointer(Box::new(CTypeLike::Void));
            }
            if scalar_score > pointer_score.saturating_add(2) {
                return fallback_scalar_type_like(var_size_bytes, evidence, ptr_bits);
            }
            return initial_ty;
        }
        _ => {}
    }

    if pointer_score > scalar_score.saturating_add(1) {
        return CTypeLike::Pointer(Box::new(CTypeLike::Void));
    }
    if scalar_score > pointer_score || matches!(initial_ty, CTypeLike::Void | CTypeLike::Unknown) {
        return preferred_scalar;
    }

    sanitize_signature_type_like(initial_ty, var_size_bytes, ptr_bits)
}

pub fn collect_signature_type_evidence_for_var(
    evidence_ctx: &SignatureTypeEvidenceContext,
    var: &SSAVar,
    initial_ty: &CTypeLike,
) -> SignatureTypeEvidence {
    let key = format!("{}_{}", var.name.to_ascii_lowercase(), var.version);
    let family = scalar_register_family_key(&var.name);
    let mut evidence = SignatureTypeEvidence::default();
    if evidence_ctx.pointer_vars.contains(&key) {
        evidence.pointer_proven = 1;
    }
    if evidence_ctx.scalar_proven_vars.contains(&key) {
        evidence.scalar_proven = 1;
    }
    if evidence_ctx.scalar_likely_vars.contains(&key) {
        evidence.scalar_likely = 1;
    }
    if evidence_ctx.bool_like_vars.contains(&key) {
        evidence.bool_like = 1;
    }
    if let Some(bits) = evidence_ctx.width_bits.get(&key) {
        evidence.width_bits = *bits;
    }
    if evidence.pointer_proven == 0
        && signal_present_for_register_family(&evidence_ctx.pointer_vars, &family, var.version)
    {
        evidence.pointer_proven = 1;
    }
    if evidence.scalar_proven == 0
        && signal_present_for_register_family(
            &evidence_ctx.scalar_proven_vars,
            &family,
            var.version,
        )
    {
        evidence.scalar_proven = 1;
    }
    if evidence.scalar_likely == 0
        && signal_present_for_register_family(
            &evidence_ctx.scalar_likely_vars,
            &family,
            var.version,
        )
    {
        evidence.scalar_likely = 1;
    }
    if evidence.bool_like == 0
        && signal_present_for_register_family(&evidence_ctx.bool_like_vars, &family, var.version)
    {
        evidence.bool_like = 1;
    }
    if evidence.width_bits == 0
        && let Some(bits) =
            width_hint_for_register_family(&evidence_ctx.width_bits, &family, var.version)
    {
        evidence.width_bits = bits;
    }
    merge_initial_signature_type_evidence(initial_ty, &mut evidence);
    evidence
}

fn signal_present_for_register_family(keys: &HashSet<String>, family: &str, version: u32) -> bool {
    keys.iter()
        .any(|key| key_matches_register_family_version(key, family, version))
}

fn width_hint_for_register_family(
    hints: &HashMap<String, u32>,
    family: &str,
    version: u32,
) -> Option<u32> {
    hints
        .iter()
        .filter(|(key, _)| key_matches_register_family_version(key, family, version))
        .map(|(_, bits)| *bits)
        .filter(|bits| *bits > 0)
        .min()
}

fn key_matches_register_family_version(key: &str, family: &str, version: u32) -> bool {
    let Some((name, version_str)) = key.rsplit_once('_') else {
        return false;
    };
    version_str.parse::<u32>().ok() == Some(version) && scalar_register_family_key(name) == family
}

pub fn infer_signature_return_type(
    func: &SSAFunction,
    type_inference: &TypeInference,
    ptr_bits: u32,
    evidence_ctx: &SignatureTypeEvidenceContext,
) -> (CTypeLike, SignatureTypeEvidence) {
    let mut candidates = Vec::new();
    let mut candidate_evidence = Vec::new();
    let mut candidate_constants = Vec::new();

    for block in func.blocks() {
        for op in &block.ops {
            let SSAOp::Return { target } = op else {
                continue;
            };

            let initial_ty = type_inference.get_type(target);
            let evidence =
                collect_signature_type_evidence_for_var(evidence_ctx, target, &initial_ty);
            let ty = resolve_evidence_driven_signature_type(
                initial_ty,
                target.size,
                ptr_bits,
                &evidence,
            );
            candidates.push(ty);
            candidate_evidence.push(evidence);
            candidate_constants.push(target.constant_bits());
        }
    }

    if candidates.is_empty() {
        return (CTypeLike::Void, SignatureTypeEvidence::default());
    }

    let mut meaningful: Vec<CTypeLike> = candidates
        .iter()
        .filter(|ty| !matches!(ty, CTypeLike::Unknown))
        .cloned()
        .collect();
    if meaningful.is_empty() {
        let fallback_evidence = candidate_evidence.into_iter().next().unwrap_or_default();
        return (
            fallback_scalar_type_like((ptr_bits / 8).max(1), &fallback_evidence, ptr_bits),
            fallback_evidence,
        );
    }
    if meaningful.iter().all(|ty| ty == &meaningful[0]) {
        return (
            meaningful.remove(0),
            candidate_evidence.into_iter().next().unwrap_or_default(),
        );
    }
    if let Some(float_ty) = meaningful
        .iter()
        .find(|ty| matches!(ty, CTypeLike::Float(_)))
        .cloned()
    {
        let evidence = candidate_evidence
            .into_iter()
            .find(|e| e.width_bits >= 32)
            .unwrap_or_default();
        return (float_ty, evidence);
    }
    if let Some((ty, evidence)) =
        scalar_return_type_join(&candidates, &candidate_evidence, &candidate_constants)
    {
        return (ty, evidence);
    }
    let evidence = candidate_evidence.into_iter().next().unwrap_or_default();
    (meaningful.remove(0), evidence)
}

fn infer_signature_return_type_from_prepared(
    prepared: &SsaArtifact,
    evidence_types: &crate::EvidenceTypes,
    ptr_bits: u32,
) -> (CTypeLike, SignatureTypeEvidence) {
    let mut return_values = prepared
        .facts()
        .certificates
        .returns
        .iter()
        .map(|certificate| {
            transparent_return_source_value(prepared, certificate.value)
                .unwrap_or(certificate.value)
        })
        .collect::<Vec<_>>();
    return_values.sort();
    return_values.dedup();
    if return_values.is_empty() {
        return (CTypeLike::Void, SignatureTypeEvidence::default());
    }

    infer_signature_return_type_from_values(prepared, &return_values, evidence_types, ptr_bits)
}

fn transparent_return_source_value(
    prepared: &SsaArtifact,
    start: r2ssa::ValueId,
) -> Option<r2ssa::ValueId> {
    let mut current = start;
    let mut visited = HashSet::new();
    while visited.insert(current) {
        let Some(inst) = prepared
            .graph()
            .def_inst(current)
            .and_then(|inst| prepared.graph().inst(inst))
        else {
            return Some(current);
        };
        let r2ssa::InstPayload::Op(op) = &inst.payload else {
            return Some(current);
        };
        match op {
            SSAOp::Copy { .. }
            | SSAOp::New { .. }
            | SSAOp::IntZExt { .. }
            | SSAOp::IntSExt { .. }
            | SSAOp::Trunc { .. }
            | SSAOp::Subpiece { offset: 0, .. } => {}
            _ => return Some(current),
        };
        let Some(source_value) = inst.inputs.first().copied() else {
            return Some(current);
        };
        current = source_value;
    }
    None
}

fn exact_signature_type_evidence(ty: &CTypeLike) -> SignatureTypeEvidence {
    let mut evidence = SignatureTypeEvidence::default();
    merge_initial_signature_type_evidence(ty, &mut evidence);
    match ty {
        CTypeLike::Pointer(_) => evidence.pointer_proven = 1,
        CTypeLike::Bool => evidence.bool_like = 1,
        CTypeLike::Float(bits) => {
            evidence.scalar_proven = 1;
            evidence.width_bits = *bits;
        }
        CTypeLike::Int { bits, .. } => evidence.width_bits = *bits,
        _ => {}
    }
    evidence
}

fn infer_signature_return_type_from_values(
    prepared: &SsaArtifact,
    return_values: &[r2ssa::ValueId],
    evidence_types: &crate::EvidenceTypes,
    ptr_bits: u32,
) -> (CTypeLike, SignatureTypeEvidence) {
    let mut candidates = Vec::new();
    let mut candidate_evidence = Vec::new();
    let mut candidate_constants = Vec::new();
    for value in return_values {
        let Some(var) = prepared.value_var(*value) else {
            continue;
        };
        let initial_ty = evidence_types
            .value_type(*value)
            .cloned()
            .unwrap_or_else(|| fallback_scalar_type_like(var.size, &Default::default(), ptr_bits));
        let evidence = exact_signature_type_evidence(&initial_ty);
        let ty = resolve_evidence_driven_signature_type(initial_ty, var.size, ptr_bits, &evidence);
        candidates.push(ty);
        candidate_evidence.push(evidence);
        candidate_constants.push(var.constant_bits());
    }
    choose_signature_return_type(
        candidates,
        candidate_evidence,
        candidate_constants,
        ptr_bits,
    )
}

fn choose_signature_return_type(
    candidates: Vec<CTypeLike>,
    candidate_evidence: Vec<SignatureTypeEvidence>,
    candidate_constants: Vec<Option<u64>>,
    ptr_bits: u32,
) -> (CTypeLike, SignatureTypeEvidence) {
    if candidates.is_empty() {
        return (CTypeLike::Void, SignatureTypeEvidence::default());
    }
    let mut meaningful = candidates
        .iter()
        .filter(|ty| !matches!(ty, CTypeLike::Unknown))
        .cloned()
        .collect::<Vec<_>>();
    if meaningful.is_empty() {
        let fallback_evidence = candidate_evidence.into_iter().next().unwrap_or_default();
        return (
            fallback_scalar_type_like((ptr_bits / 8).max(1), &fallback_evidence, ptr_bits),
            fallback_evidence,
        );
    }
    if meaningful.iter().all(|ty| ty == &meaningful[0]) {
        return (
            meaningful.remove(0),
            candidate_evidence.into_iter().next().unwrap_or_default(),
        );
    }
    if let Some(float_ty) = meaningful
        .iter()
        .find(|ty| matches!(ty, CTypeLike::Float(_)))
        .cloned()
    {
        let evidence = candidate_evidence
            .into_iter()
            .find(|evidence| evidence.width_bits >= 32)
            .unwrap_or_default();
        return (float_ty, evidence);
    }
    if let Some((ty, evidence)) =
        scalar_return_type_join(&candidates, &candidate_evidence, &candidate_constants)
    {
        return (ty, evidence);
    }
    let evidence = candidate_evidence.into_iter().next().unwrap_or_default();
    (meaningful.remove(0), evidence)
}

fn scalar_return_type_join(
    candidates: &[CTypeLike],
    evidence: &[SignatureTypeEvidence],
    constants: &[Option<u64>],
) -> Option<(CTypeLike, SignatureTypeEvidence)> {
    if candidates.len() != evidence.len() || candidates.len() != constants.len() {
        return None;
    }

    let mut semantic_width = candidates
        .iter()
        .zip(constants)
        .filter_map(|(ty, constant)| match (ty, constant) {
            (CTypeLike::Int { bits, .. }, None) => Some(*bits),
            _ => None,
        })
        .max()?;

    for (ty, constant) in candidates.iter().zip(constants) {
        let CTypeLike::Int { bits, .. } = ty else {
            return None;
        };
        if *bits > semantic_width
            && !constant.is_some_and(|value| unsigned_value_fits_bits(value, semantic_width))
        {
            semantic_width = *bits;
        }
    }

    let mut saw_signed = false;
    let mut saw_unsigned = false;
    let mut saw_unknown = false;
    for (ty, constant) in candidates.iter().zip(constants) {
        if constant.is_some() {
            continue;
        }
        let CTypeLike::Int { signedness, .. } = ty else {
            return None;
        };
        match signedness {
            Signedness::Signed => saw_signed = true,
            Signedness::Unsigned => saw_unsigned = true,
            Signedness::Unknown => saw_unknown = true,
        }
    }
    let signedness = if saw_signed {
        Signedness::Signed
    } else if saw_unknown {
        Signedness::Unknown
    } else if saw_unsigned {
        Signedness::Unsigned
    } else {
        return None;
    };

    let mut joined_evidence = SignatureTypeEvidence::default();
    for item in evidence {
        joined_evidence.pointer_proven = joined_evidence.pointer_proven.max(item.pointer_proven);
        joined_evidence.pointer_likely = joined_evidence.pointer_likely.max(item.pointer_likely);
        joined_evidence.scalar_proven = joined_evidence.scalar_proven.max(item.scalar_proven);
        joined_evidence.scalar_likely = joined_evidence.scalar_likely.max(item.scalar_likely);
        joined_evidence.bool_like = joined_evidence.bool_like.max(item.bool_like);
    }
    joined_evidence.width_bits = semantic_width;

    Some((
        CTypeLike::Int {
            bits: semantic_width,
            signedness,
        },
        joined_evidence,
    ))
}

fn unsigned_value_fits_bits(value: u64, bits: u32) -> bool {
    bits >= 64 || (bits > 0 && value < (1u64 << bits))
}

fn canonical_x86_64_arg_reg(name: &str) -> Option<&'static str> {
    match name.to_ascii_lowercase().as_str() {
        "rdi" | "edi" | "di" | "dil" => Some("rdi"),
        "rsi" | "esi" | "si" | "sil" => Some("rsi"),
        "rdx" | "edx" | "dx" | "dl" | "dh" => Some("rdx"),
        "rcx" | "ecx" | "cx" | "cl" | "ch" => Some("rcx"),
        "r8" | "r8d" | "r8w" | "r8b" => Some("r8"),
        "r9" | "r9d" | "r9w" | "r9b" => Some("r9"),
        _ => None,
    }
}

pub fn collect_version0_input_regs(func: &SSAFunction) -> HashMap<String, u32> {
    let mut counts = HashMap::new();
    for block in func.blocks() {
        for op in &block.ops {
            for src in op.sources() {
                if src.version != 0 {
                    continue;
                }
                if !ssa_var_is_register_like(src) {
                    continue;
                }
                let key = src.name.to_ascii_lowercase();
                *counts.entry(key).or_insert(0) += 1;
            }
        }
    }
    counts
}

fn infer_callconv_x86_64_from_counts(counts: &HashMap<String, u32>) -> (&'static str, u8) {
    let mut canonical = std::collections::BTreeMap::new();
    for (reg, count) in counts {
        if let Some(name) = canonical_x86_64_arg_reg(reg) {
            *canonical.entry(name).or_insert(0u32) += *count;
        }
    }

    let rdi = *canonical.get("rdi").unwrap_or(&0);
    let rsi = *canonical.get("rsi").unwrap_or(&0);
    let rcx = *canonical.get("rcx").unwrap_or(&0);
    let rdx = *canonical.get("rdx").unwrap_or(&0);
    let r8 = *canonical.get("r8").unwrap_or(&0);
    let r9 = *canonical.get("r9").unwrap_or(&0);

    let sysv_primary = rdi + rsi;
    let sysv_total = rdi + rsi + rdx + rcx + r8 + r9;
    let ms_total = rcx + rdx + r8 + r9;
    let ms_regs_used = [rcx, rdx, r8, r9].iter().filter(|&&v| v > 0).count();
    let ms_dominant = sysv_primary == 0
        && rcx > 0
        && ms_regs_used >= 2
        && ms_total >= 3
        && ms_total >= (rdi + rsi + rdx + 1);

    if ms_dominant {
        let confidence = if ms_total >= 3 { 90 } else { 76 };
        ("ms", confidence)
    } else {
        let confidence = if sysv_primary > 0 {
            92
        } else if sysv_total > 0 {
            76
        } else {
            60
        };
        ("amd64", confidence)
    }
}

pub fn compute_callconv_inference(
    arch_name: &str,
    input_counts: &HashMap<String, u32>,
) -> (String, u8) {
    match arch_name {
        "x86-64" => {
            let (callconv, confidence) = infer_callconv_x86_64_from_counts(input_counts);
            (callconv.to_string(), confidence)
        }
        "x86" => ("cdecl".to_string(), 64),
        _ => (String::new(), 0),
    }
}

fn is_informative_type(ty: &CTypeLike) -> bool {
    !matches!(ty, CTypeLike::Void | CTypeLike::Unknown)
}

pub fn compute_signature_confidence(
    params: &[SignatureParamCandidate],
    ret_type: &CTypeLike,
    ret_evidence: &SignatureTypeEvidence,
) -> u8 {
    let mut confidence: i32 = 48;
    if !params.is_empty() {
        confidence += 8;
    }

    for param in params {
        let evidence = &param.evidence;
        if evidence.pointer_proven > 0 || evidence.scalar_proven > 0 {
            confidence += 6;
        } else if evidence.bool_like > 0
            || evidence.pointer_likely > 0
            || evidence.scalar_likely > 0
        {
            confidence += 3;
        } else if is_informative_type(&param.ty) {
            confidence += 2;
        } else {
            confidence -= 2;
        }

        if evidence.has_conflict() {
            confidence -= 4;
        }
    }

    if is_informative_type(ret_type) {
        confidence += 4;
        if ret_evidence.pointer_proven > 0
            || ret_evidence.scalar_proven > 0
            || ret_evidence.bool_like > 0
        {
            confidence += 2;
        }
    } else if ret_evidence.has_pointer_signal() || ret_evidence.has_scalar_signal() {
        confidence += 2;
    }

    if ret_evidence.has_conflict() {
        confidence -= 3;
    }

    confidence.clamp(0, 100) as u8
}

fn sanitize_c_identifier(name: &str) -> Option<String> {
    let mut out = String::with_capacity(name.len());
    for (idx, ch) in name.chars().enumerate() {
        let mapped = if ch.is_ascii_alphanumeric() || ch == '_' {
            ch
        } else {
            '_'
        };
        if idx == 0 && mapped.is_ascii_digit() {
            out.push('_');
        }
        out.push(mapped);
    }
    let trimmed = out.trim_matches('_').to_string();
    if trimmed.is_empty() {
        None
    } else {
        Some(trimmed)
    }
}

fn uniquify_name(base: String, used: &mut HashSet<String>) -> String {
    if used.insert(base.clone()) {
        return base;
    }
    let mut index = 1usize;
    loop {
        let candidate = format!("{base}_{index}");
        if used.insert(candidate.clone()) {
            return candidate;
        }
        index += 1;
    }
}

fn normalize_inferred_param_name(
    raw_name: &str,
    fallback_idx: usize,
    used: &mut HashSet<String>,
) -> String {
    let fallback = format!("arg{}", fallback_idx);
    let clean = sanitize_c_identifier(raw_name).unwrap_or_else(|| fallback.clone());
    let clean = if clean.is_empty() { fallback } else { clean };
    uniquify_name(clean, used)
}

pub fn format_afs_signature(
    function_name: &str,
    ret_type: &str,
    params: &[InferredSignatureParam],
) -> String {
    let params_str = if params.is_empty() {
        "void".to_string()
    } else {
        params
            .iter()
            .map(|p| format!("{} {}", p.param_type, p.name))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!("{ret_type} {function_name} ({params_str})")
}

pub fn inferred_signature_from_signature_spec(
    function_name: &str,
    arch_name: &str,
    ptr_bits: u32,
    callconv: Option<&str>,
    signature: &FunctionSignatureSpec,
) -> InferredSignature {
    let ret_type = signature
        .ret_type
        .as_ref()
        .map(|ty| render_signature_type(ty, ptr_bits))
        .unwrap_or_else(|| "void".to_string());
    let params = signature
        .params
        .iter()
        .enumerate()
        .map(|(idx, param)| InferredSignatureParam {
            name: if param.name.trim().is_empty() {
                format!("arg{}", idx + 1)
            } else {
                param.name.clone()
            },
            param_type: param
                .ty
                .as_ref()
                .map(|ty| render_signature_type(ty, ptr_bits))
                .unwrap_or_else(|| "void *".to_string()),
        })
        .collect::<Vec<_>>();
    let callconv = callconv.unwrap_or("unknown").to_string();
    let callconv_confidence = if callconv == "unknown" { 0 } else { 80 };
    InferredSignature {
        function_name: function_name.to_string(),
        signature: format_afs_signature(function_name, &ret_type, &params),
        ret_type,
        params,
        callconv,
        arch: arch_name.to_string(),
        confidence: signature_strength(signature),
        callconv_confidence,
    }
}

pub fn build_inferred_signature(
    function_name: &str,
    arch_name: &str,
    ptr_bits: u32,
    params: &[SignatureParamCandidate],
    ret_type: &CTypeLike,
    ret_evidence: &SignatureTypeEvidence,
    input_counts: &HashMap<String, u32>,
) -> InferredSignature {
    let mut ordered = params.to_vec();
    ordered.sort_by(|a, b| {
        a.arg_index
            .cmp(&b.arg_index)
            .then_with(|| a.name.cmp(&b.name))
    });
    let confidence = compute_signature_confidence(&ordered, ret_type, ret_evidence);
    let mut used_param_names = HashSet::new();
    let mut json_params = Vec::new();
    for param in &ordered {
        let slot = if param.arg_index == usize::MAX {
            json_params.len()
        } else {
            param.arg_index
        };
        while json_params.len() < slot {
            let gap_slot = json_params.len();
            json_params.push(InferredSignatureParam {
                name: normalize_inferred_param_name(
                    &format!("arg{gap_slot}"),
                    gap_slot,
                    &mut used_param_names,
                ),
                param_type: render_signature_type(
                    &CTypeLike::Int {
                        bits: ptr_bits.max(8),
                        signedness: Signedness::Unknown,
                    },
                    ptr_bits,
                ),
            });
        }
        json_params.push(InferredSignatureParam {
            name: normalize_inferred_param_name(&param.name, slot, &mut used_param_names),
            param_type: render_signature_type(&param.ty, ptr_bits),
        });
    }
    let rendered_ret = render_signature_type(ret_type, ptr_bits);
    let (callconv, callconv_confidence) = compute_callconv_inference(arch_name, input_counts);
    InferredSignature {
        function_name: function_name.to_string(),
        signature: format_afs_signature(function_name, &rendered_ret, &json_params),
        ret_type: rendered_ret,
        params: json_params,
        callconv,
        arch: arch_name.to_string(),
        confidence,
        callconv_confidence,
    }
}

/// Record a prototype under every spelling of the name it was found by.
///
/// A prototype already recorded for a spelling was declared, not looked up, so
/// it stays: what radare2 or the user says a function takes outranks what a
/// name resolves to.
fn insert_known_signature_aliases(
    known: &mut HashMap<String, FunctionType>,
    name: &str,
    sig: &FunctionType,
) {
    if name.is_empty() {
        return;
    }
    known.entry(name.to_string()).or_insert_with(|| sig.clone());

    for prefix in ["sym.imp.", "sym.", "imp.", "dbg.", "fcn."] {
        if let Some(stripped) = name.strip_prefix(prefix)
            && !stripped.is_empty()
        {
            known
                .entry(stripped.to_string())
                .or_insert_with(|| sig.clone());
        }
    }
}

/// The registry spelling a linker name stands for.
///
/// An import table spells one function many ways: a namespace prefix, a symbol
/// version suffix, a libc-internal alias. Stripping those is safe because none
/// of them change the prototype. Collapsing a fortified `__*_chk` name onto its
/// base function is not: the fortified form takes an extra destination-size
/// argument, so a caller that trusted the base arity would drop it. Those carry
/// their own prototypes in the registry instead.
fn signature_registry_alias(name: &str) -> Option<String> {
    let lowered = name.trim().to_ascii_lowercase();
    let mut normalized = lowered.as_str();

    for prefix in ["sym.imp.", "sym.", "imp.", "reloc.", "dbg."] {
        while let Some(rest) = normalized.strip_prefix(prefix) {
            normalized = rest;
        }
    }

    while let Some(rest) = normalized.strip_suffix("@plt") {
        normalized = rest;
    }
    while let Some(rest) = normalized.strip_suffix(".plt") {
        normalized = rest;
    }
    if let Some((base, _)) = normalized.split_once('@') {
        normalized = base;
    }

    if let Some(rest) = normalized.strip_prefix("__isoc99_") {
        normalized = rest;
    }
    if let Some(rest) = normalized.strip_prefix("__gi_") {
        normalized = rest;
    }

    // Different linker name, same prototype.
    let normalized = match normalized {
        "__libc_malloc" => "malloc",
        "_exit" => "exit",
        other => other,
    };

    (normalized != name).then(|| normalized.to_string())
}

/// The prototypes the embedded registry holds for these names.
///
/// A call to a libc function radare2 has no type for reaches inference with no
/// prototype at all, so neither its argument types nor its arity are known. The
/// registry answer is the whole prototype or nothing: a name that resolves gets
/// its real parameter list, including the trailing destination size a fortified
/// `__*_chk` entry point takes, so an arity cap built from it cannot swallow an
/// argument the call really passes.
///
/// These are looked up from a name, so they are the weakest prototype there is.
/// The caller decides what they may fill in; they never displace a prototype
/// radare2 or the user already declared.
pub fn enrich_known_function_signatures_from_names<I, N>(
    known: &mut HashMap<String, FunctionType>,
    function_names: I,
    ptr_bits: u32,
) where
    I: IntoIterator<Item = N>,
    N: AsRef<str>,
{
    let registry = SignatureRegistry::from_embedded_json();
    let mut arena = crate::TypeArena::default();

    for name in function_names {
        let name = name.as_ref();
        let alias = signature_registry_alias(name);
        let resolved = [Some(name), alias.as_deref()]
            .into_iter()
            .flatten()
            .find_map(|candidate| {
                registry
                    .resolve(candidate, &mut arena, ptr_bits)
                    .map(|resolved| (candidate, resolved))
            });

        let Some((resolved_name, resolved)) = resolved else {
            continue;
        };
        let sig = FunctionType {
            return_type: crate::to_c_type_like(&arena, resolved.ret),
            params: resolved
                .params
                .iter()
                .map(|param| crate::to_c_type_like(&arena, *param))
                .collect(),
            variadic: resolved.variadic,
        };

        insert_known_signature_aliases(known, name, &sig);
        if resolved_name != name {
            insert_known_signature_aliases(known, resolved_name, &sig);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x86_return_arch() -> r2il::ArchSpec {
        let mut arch = r2il::ArchSpec::new("x86-64");
        arch.add_register(r2il::RegisterDef::new("RAX", 0, 8));
        arch.add_register(r2il::RegisterDef::new("RIP", 8, 8));
        arch.add_register(r2il::RegisterDef::new("RSP", 16, 8));
        arch
    }

    fn prepared_x86_scalar_return(
        return_carrier_name: &str,
        calling_convention: &str,
    ) -> SsaArtifact {
        let mut arch = r2il::ArchSpec::new("x86-64");
        arch.add_register(r2il::RegisterDef::new(return_carrier_name, 0, 8));
        arch.add_register(r2il::RegisterDef::new("RIP", 8, 8));
        arch.add_register(r2il::RegisterDef::new("RSP", 16, 8));
        let register = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            format!("signature-{return_carrier_name}").into_bytes(),
            calling_convention,
            [],
            r2ssa::SourceFunctionReturn::Register {
                storage: register(0),
            },
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(register(8)))
        .and_then(|interface| interface.with_stack_pointer_storage(register(16)))
        .expect("exact renamed return interface");
        let mut block = r2il::R2ILBlock::new(0x1000, 4);
        block.push(r2il::R2ILOp::IntZExt {
            dst: r2il::Varnode::register(0, 8),
            src: r2il::Varnode::unique(0x20, 4),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(8, 8),
        });
        SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("prepared renamed return source")
    }

    fn aarch64_parameter_arch() -> r2il::ArchSpec {
        let mut arch = r2il::ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(r2il::RegisterDef::new("x0", 0, 8));
        arch.add_register(r2il::RegisterDef::new("w0", 0, 4));
        arch.add_register(r2il::RegisterDef::new("sp", 16, 8));
        arch.add_register(r2il::RegisterDef::new("lr", 24, 8));
        arch
    }

    fn aarch64_prepared_with_stack_slot(
        block: r2il::R2ILBlock,
        stack_slot: r2ssa::SourceStackSlotSpec,
    ) -> SsaArtifact {
        let register_storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let parameter = register_storage(0);
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"aarch64-stack-fixture".to_vec(),
            "aarch64",
            [r2ssa::SourceAbiParameterSpec::new(0, parameter)],
            r2ssa::SourceFunctionReturn::Void,
            [stack_slot],
        )
        .and_then(|interface| interface.with_return_address_storage(register_storage(24)))
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(16)))
        .expect("exact AArch64 stack interface");
        SsaArtifact::for_decompile_with_interface(
            &[block],
            Some(&aarch64_parameter_arch()),
            interface,
        )
        .expect("prepared exact AArch64 stack fixture")
    }

    #[test]
    fn prepared_signature_recovers_unsigned_byte_pointee_through_certified_stack_reload() {
        let mut block = r2il::R2ILBlock::new(0x1000, 4);
        block.push(r2il::R2ILOp::IntSub {
            dst: r2il::Varnode::unique(0x10, 8),
            a: r2il::Varnode::register(16, 8),
            b: r2il::Varnode::constant(8, 8),
        });
        block.push(r2il::R2ILOp::Load {
            dst: r2il::Varnode::unique(0x20, 1),
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::register(0, 8),
        });
        block.push(r2il::R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x10, 8),
            val: r2il::Varnode::unique(0x20, 1),
        });
        block.push(r2il::R2ILOp::Load {
            dst: r2il::Varnode::unique(0x30, 1),
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x10, 8),
        });
        block.push(r2il::R2ILOp::IntZExt {
            dst: r2il::Varnode::unique(0x40, 4),
            src: r2il::Varnode::unique(0x30, 1),
        });
        let prepared = aarch64_prepared_with_stack_slot(
            block,
            r2ssa::SourceStackSlotSpec::new_local(
                r2ssa::StackAddressBase::StackPointer,
                r2ssa::CanonicalStorageId {
                    space: r2ssa::CanonicalStorageSpace::Register,
                    offset: 16,
                    size: 8,
                },
                -8,
                1,
            ),
        );
        let inferred = infer_signature_from_prepared_ssa(&prepared);

        assert_eq!(inferred.arch, "aarch64");
        assert_eq!(inferred.params[0].param_type, "uint8_t*");
    }

    #[test]
    fn prepared_signature_recovers_unsigned_scalar_through_certified_stack_reload() {
        let mut block = r2il::R2ILBlock::new(0x1000, 4);
        block.push(r2il::R2ILOp::IntSub {
            dst: r2il::Varnode::unique(0x10, 8),
            a: r2il::Varnode::register(16, 8),
            b: r2il::Varnode::constant(8, 8),
        });
        block.push(r2il::R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x10, 8),
            val: r2il::Varnode::register(0, 8),
        });
        block.push(r2il::R2ILOp::Load {
            dst: r2il::Varnode::unique(0x20, 8),
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x10, 8),
        });
        block.push(r2il::R2ILOp::IntLess {
            dst: r2il::Varnode::unique(0x30, 1),
            a: r2il::Varnode::unique(0x20, 8),
            b: r2il::Varnode::constant(10, 8),
        });
        block.push(r2il::R2ILOp::CBranch {
            target: r2il::Varnode::constant(0x2000, 8),
            cond: r2il::Varnode::unique(0x30, 1),
        });
        let stack_pointer = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: 16,
            size: 8,
        };
        let parameter = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        let prepared = aarch64_prepared_with_stack_slot(
            block,
            r2ssa::SourceStackSlotSpec::new_parameter_home(
                r2ssa::StackAddressBase::StackPointer,
                stack_pointer,
                -8,
                8,
                0,
                parameter,
            ),
        );
        let inferred = infer_signature_from_prepared_ssa(&prepared);

        assert_eq!(inferred.params[0].param_type, "uint64_t");
    }

    #[test]
    fn overwritten_stack_home_does_not_alias_parameter_signedness() {
        let mut block = r2il::R2ILBlock::new(0x1000, 4);
        block.push(r2il::R2ILOp::IntSub {
            dst: r2il::Varnode::unique(0x10, 8),
            a: r2il::Varnode::register(16, 8),
            b: r2il::Varnode::constant(8, 8),
        });
        block.push(r2il::R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x10, 8),
            val: r2il::Varnode::register(0, 8),
        });
        block.push(r2il::R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x10, 8),
            val: r2il::Varnode::constant(1, 8),
        });
        block.push(r2il::R2ILOp::Load {
            dst: r2il::Varnode::unique(0x20, 8),
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x10, 8),
        });
        let stack_pointer = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: 16,
            size: 8,
        };
        let parameter = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        let prepared = aarch64_prepared_with_stack_slot(
            block,
            r2ssa::SourceStackSlotSpec::new_parameter_home(
                r2ssa::StackAddressBase::StackPointer,
                stack_pointer,
                -8,
                8,
                0,
                parameter,
            ),
        );
        let recovered = [RecoveredSignatureParam {
            name: "value".to_string(),
            arg_index: 0,
            ssa_var: SSAVar::new("x0", 0, 8),
            initial_ty: CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Unknown,
            },
        }];

        assert!(certified_parameter_home_aliases(&prepared, &recovered).is_empty());
    }

    #[test]
    fn prepared_signature_uses_certified_return_value_not_control_target() {
        let arch = x86_return_arch();
        let mut block = r2il::R2ILBlock::new(0x1000, 4);
        block.push(r2il::R2ILOp::IntZExt {
            dst: r2il::Varnode::register(0, 8),
            src: r2il::Varnode::unique(0x20, 4),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(8, 8),
        });
        let return_storage = r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"certified-signature-return-fixture".to_vec(),
            "sysv64",
            [],
            r2ssa::SourceFunctionReturn::Register {
                storage: return_storage,
            },
            [],
        )
        .and_then(|interface| {
            interface.with_return_address_storage(r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: 8,
                size: 8,
            })
        })
        .and_then(|interface| {
            interface.with_stack_pointer_storage(r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: 16,
                size: 8,
            })
        })
        .expect("exact function return interface");
        let prepared = SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("prepared exact return SSA");
        assert_eq!(
            prepared.certificates().returns.len(),
            1,
            "source-owned return fixture must certify one value"
        );
        let inferred = infer_signature_from_prepared_ssa(&prepared);

        assert_eq!(inferred.ret_type, "uint32_t");
    }

    #[test]
    fn prepared_signature_callconv_is_source_owned_and_rename_invariant() {
        let expected = "source-owned-test-cc";
        let ordinary =
            infer_signature_from_prepared_ssa(&prepared_x86_scalar_return("rax", expected));
        let renamed = infer_signature_from_prepared_ssa(&prepared_x86_scalar_return(
            "xmm0_misleading",
            expected,
        ));

        assert_eq!(ordinary.callconv, expected);
        assert_eq!(renamed.callconv, expected);
        assert_eq!(ordinary.callconv_confidence, 100);
        assert_eq!(renamed.callconv_confidence, 100);
    }

    #[test]
    fn misleading_xmm0_spelling_does_not_manufacture_a_float_return() {
        let inferred = infer_signature_from_prepared_ssa(&prepared_x86_scalar_return(
            "xmm0_misleading",
            "source-owned-test-cc",
        ));

        assert_eq!(inferred.ret_type, "uint32_t");
        assert_ne!(inferred.ret_type, "float");
        assert_ne!(inferred.ret_type, "double");
    }

    #[test]
    fn prepared_signature_does_not_type_void_return_from_program_counter() {
        let arch = x86_return_arch();
        let mut block = r2il::R2ILBlock::new(0x1000, 4);
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(8, 8),
        });
        let prepared = SsaArtifact::for_patterns(&[block], Some(&arch)).expect("prepared SSA");
        let inferred = infer_signature_from_prepared_ssa(&prepared);

        assert_eq!(inferred.ret_type, "void");
    }

    #[test]
    fn scalar_return_join_narrows_wide_constant_to_nonconstant_semantic_width() {
        let candidates = vec![
            CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed,
            },
            CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            },
        ];
        let evidence = vec![
            SignatureTypeEvidence {
                scalar_likely: 1,
                width_bits: 64,
                ..Default::default()
            },
            SignatureTypeEvidence {
                scalar_proven: 1,
                width_bits: 32,
                ..Default::default()
            },
        ];

        let (ty, joined_evidence) =
            scalar_return_type_join(&candidates, &evidence, &[Some(0xffff_ffff), None])
                .expect("integer return join");

        assert_eq!(
            ty,
            CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }
        );
        assert_eq!(joined_evidence.width_bits, 32);
        assert_eq!(joined_evidence.scalar_proven, 1);
    }

    #[test]
    fn scalar_return_join_keeps_genuine_wide_nonconstant_path() {
        let candidates = vec![
            CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            },
            CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed,
            },
        ];
        let evidence = vec![SignatureTypeEvidence::default(); 2];

        let (ty, _) = scalar_return_type_join(&candidates, &evidence, &[None, None])
            .expect("integer return join");

        assert_eq!(
            ty,
            CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed,
            }
        );
    }

    #[test]
    fn enrich_known_function_signatures_keeps_fortified_arity() {
        let mut known = HashMap::new();

        enrich_known_function_signatures_from_names(&mut known, ["sym.imp.__memcpy_chk"], 64);

        let signature = known
            .get("__memcpy_chk")
            .expect("fortified prototype missing");
        // memcpy's three arguments plus the destination size the fortified
        // entry point takes. Answering with memcpy's arity would cap a real
        // four-argument call at three and drop the size the call passes.
        assert_eq!(signature.params.len(), 4);
        assert!(!signature.variadic);
        assert!(known.contains_key("sym.imp.__memcpy_chk"));
        assert!(!known.contains_key("memcpy"));
    }

    #[test]
    fn enrich_known_function_signatures_does_not_displace_a_declared_prototype() {
        let declared = FunctionType {
            return_type: CTypeLike::Void,
            params: Vec::new(),
            variadic: false,
        };
        let mut known = HashMap::from([("memcpy".to_string(), declared.clone())]);

        enrich_known_function_signatures_from_names(&mut known, ["sym.imp.memcpy"], 64);

        assert_eq!(known.get("memcpy"), Some(&declared));
    }

    #[test]
    fn enrich_known_function_signatures_reads_through_linker_spellings() {
        let mut known = HashMap::new();

        enrich_known_function_signatures_from_names(
            &mut known,
            ["reloc.__libc_malloc@GLIBC_2.2.5", "sym.imp.__printf_chk"],
            64,
        );

        assert!(known.contains_key("malloc"));
        let printf_chk = known
            .get("__printf_chk")
            .expect("fortified printf prototype missing");
        // The leading `int flag` is not printf's format pointer.
        assert!(matches!(
            printf_chk.params.first(),
            Some(CTypeLike::Int { bits: 32, .. })
        ));
        assert!(printf_chk.variadic);
    }

    #[test]
    fn inferred_signature_from_signature_spec_materializes_callconv_and_types() {
        let signature = FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Void),
            params: vec![crate::FunctionParamSpec {
                name: "status".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 32,
                    signedness: Signedness::Signed,
                }),
            }],
        };

        let inferred = inferred_signature_from_signature_spec(
            "fcn.401000",
            "x86-64",
            64,
            Some("amd64"),
            &signature,
        );

        assert_eq!(inferred.signature, "void fcn.401000 (int32_t status)");
        assert_eq!(inferred.callconv, "amd64");
        assert_eq!(
            inferred.confidence,
            crate::SIGNATURE_PROJECTION_STRONG_CONFIDENCE
        );
    }

    #[test]
    fn sparse_abi_parameters_materialize_preceding_slots() {
        let params = vec![
            SignatureParamCandidate {
                name: "arg0".to_string(),
                ty: CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Unknown,
                },
                arg_index: 0,
                size_bytes: 8,
                evidence: SignatureTypeEvidence::default(),
            },
            SignatureParamCandidate {
                name: "arg6".to_string(),
                ty: CTypeLike::Int {
                    bits: 32,
                    signedness: Signedness::Signed,
                },
                arg_index: 6,
                size_bytes: 4,
                evidence: SignatureTypeEvidence {
                    scalar_proven: 1,
                    width_bits: 32,
                    ..SignatureTypeEvidence::default()
                },
            },
        ];

        let inferred = build_inferred_signature(
            "stack_arg",
            "x86-64",
            64,
            &params,
            &CTypeLike::Void,
            &SignatureTypeEvidence::default(),
            &HashMap::new(),
        );

        assert_eq!(inferred.params.len(), 7);
        for (slot, param) in inferred.params.iter().enumerate() {
            assert_eq!(param.name, format!("arg{slot}"));
        }
        assert_eq!(inferred.params[1].param_type, "int64_t");
        assert_eq!(inferred.params[6].param_type, "int32_t");
    }
}
