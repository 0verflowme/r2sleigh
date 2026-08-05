use std::collections::{BTreeSet, HashMap, HashSet};

use r2ssa::{SSABlock, SSAFunction, SSAOp, SSAVar, SsaArtifact};

use crate::convert::CTypeLike;
use crate::facts::{FunctionSignatureSpec, FunctionType, FunctionTypeFacts, signature_strength};
use crate::inference::TypeInference;
use crate::model::Signedness;
use crate::prepare::{
    SignatureTypeEvidenceContext, scalar_register_family_key, ssa_var_is_register_like,
};
use crate::signature::SignatureRegistry;
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
    pub ssa_var: SSAVar,
    pub initial_ty: CTypeLike,
}

pub fn merge_pointer_slot_evidence_into_signature_params(
    inferred_params: &mut [SignatureParamCandidate],
    pointer_arg_slots: &BTreeSet<usize>,
) {
    if pointer_arg_slots.is_empty() {
        return;
    }

    let param_count = inferred_params.len();
    for (fallback_idx, param) in inferred_params.iter_mut().enumerate() {
        let explicit_slot = if param.arg_index == usize::MAX {
            None
        } else {
            Some(param.arg_index)
        };
        let slot = explicit_slot.unwrap_or(fallback_idx);
        let fallback_slot_match = pointer_arg_slots.contains(&fallback_idx)
            && (explicit_slot.is_none() || param_count == 1);
        if pointer_arg_slots.contains(&slot) || fallback_slot_match {
            param.evidence.pointer_proven = param.evidence.pointer_proven.max(1);
        }
    }
}

pub fn infer_signature_from_prepared_ssa(
    function_name: &str,
    arch_name: &str,
    ptr_bits: u32,
    prepared: &SsaArtifact,
    pattern_ssa_blocks: &[SSABlock],
    recovered_params: &[RecoveredSignatureParam],
    pointer_arg_slots: &BTreeSet<usize>,
) -> InferredSignature {
    let evidence_ctx = crate::prepare::collect_signature_type_evidence_context(pattern_ssa_blocks);
    let mut type_inference = TypeInference::new(ptr_bits);
    type_inference.set_prepared_ssa(prepared);
    type_inference.infer_function(prepared);

    let mut canonical_params = recovered_params
        .iter()
        .map(|param| {
            let mut evidence = collect_signature_type_evidence_for_var(
                &evidence_ctx,
                &param.ssa_var,
                &param.initial_ty,
            );
            if matches!(param.initial_ty, CTypeLike::Void | CTypeLike::Unknown) {
                merge_initial_signature_type_evidence(
                    &type_inference.type_from_size(param.ssa_var.size),
                    &mut evidence,
                );
            }
            let ty = resolve_evidence_driven_signature_type(
                param.initial_ty.clone(),
                param.ssa_var.size,
                ptr_bits,
                &evidence,
            );
            let arg_index = param
                .name
                .strip_prefix("arg")
                .and_then(|n| n.parse::<usize>().ok())
                .unwrap_or(usize::MAX);
            SignatureParamCandidate {
                name: param.name.clone(),
                ty,
                arg_index,
                size_bytes: param.ssa_var.size,
                evidence,
            }
        })
        .collect::<Vec<_>>();

    merge_pointer_slot_evidence_into_signature_params(&mut canonical_params, pointer_arg_slots);

    for param in &mut canonical_params {
        param.ty = resolve_evidence_driven_signature_type(
            param.ty.clone(),
            param.size_bytes,
            ptr_bits,
            &param.evidence,
        );
    }

    let (ret_type, ret_evidence) = infer_signature_return_type_from_prepared(
        prepared,
        &type_inference,
        ptr_bits,
        &evidence_ctx,
    );
    let input_counts = collect_version0_input_regs(prepared);
    build_inferred_signature(
        function_name,
        arch_name,
        ptr_bits,
        &canonical_params,
        &ret_type,
        &ret_evidence,
        &input_counts,
    )
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

    for block in func.blocks() {
        for op in &block.ops {
            let SSAOp::Return { target } = op else {
                continue;
            };

            let target_name = target.name.to_ascii_lowercase();
            if target_name.starts_with("xmm0") || target_name.starts_with("st0") {
                let bits = if target.size.saturating_mul(8) <= 32 {
                    32
                } else {
                    64
                };
                let ty = CTypeLike::Float(bits);
                let mut evidence = SignatureTypeEvidence::default();
                merge_initial_signature_type_evidence(&ty, &mut evidence);
                evidence.width_bits = bits;
                candidates.push(ty);
                candidate_evidence.push(evidence);
                continue;
            }

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
    let evidence = candidate_evidence.into_iter().next().unwrap_or_default();
    (meaningful.remove(0), evidence)
}

fn infer_signature_return_type_from_prepared(
    prepared: &SsaArtifact,
    type_inference: &TypeInference,
    ptr_bits: u32,
    evidence_ctx: &SignatureTypeEvidenceContext,
) -> (CTypeLike, SignatureTypeEvidence) {
    let mut return_vars = prepared
        .facts()
        .certificates
        .returns
        .iter()
        .filter_map(|certificate| {
            transparent_return_source(prepared, certificate.value)
                .or_else(|| prepared.value_var(certificate.value).cloned())
        })
        .collect::<Vec<_>>();
    return_vars.sort_by(|left, right| {
        left.name
            .cmp(&right.name)
            .then(left.version.cmp(&right.version))
            .then(left.size.cmp(&right.size))
    });
    return_vars.dedup();
    if return_vars.is_empty() {
        return (CTypeLike::Void, SignatureTypeEvidence::default());
    }

    infer_signature_return_type_from_vars(&return_vars, type_inference, ptr_bits, evidence_ctx)
}

fn transparent_return_source(prepared: &SsaArtifact, start: r2ssa::ValueId) -> Option<SSAVar> {
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
            SSAOp::Copy { src, .. }
            | SSAOp::New { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. } => src,
            SSAOp::Subpiece { src, offset, .. } if *offset == 0 => src,
            _ => return Some(current_var),
        };
        let Some(source_value) = prepared.graph().value_id_for_var(source) else {
            return Some(current_var);
        };
        current = source_value;
    }
    None
}

fn infer_signature_return_type_from_vars(
    return_vars: &[SSAVar],
    type_inference: &TypeInference,
    ptr_bits: u32,
    evidence_ctx: &SignatureTypeEvidenceContext,
) -> (CTypeLike, SignatureTypeEvidence) {
    let mut candidates = Vec::new();
    let mut candidate_evidence = Vec::new();
    for value in return_vars {
        let target_name = value.name.to_ascii_lowercase();
        if target_name.starts_with("xmm0") || target_name.starts_with("st0") {
            let bits = if value.size.saturating_mul(8) <= 32 {
                32
            } else {
                64
            };
            let ty = CTypeLike::Float(bits);
            let mut evidence = SignatureTypeEvidence::default();
            merge_initial_signature_type_evidence(&ty, &mut evidence);
            evidence.width_bits = bits;
            candidates.push(ty);
            candidate_evidence.push(evidence);
            continue;
        }

        let initial_ty = type_inference.get_type(value);
        let evidence = collect_signature_type_evidence_for_var(evidence_ctx, value, &initial_ty);
        let ty =
            resolve_evidence_driven_signature_type(initial_ty, value.size, ptr_bits, &evidence);
        candidates.push(ty);
        candidate_evidence.push(evidence);
    }
    choose_signature_return_type(candidates, candidate_evidence, ptr_bits)
}

fn choose_signature_return_type(
    candidates: Vec<CTypeLike>,
    candidate_evidence: Vec<SignatureTypeEvidence>,
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
    let evidence = candidate_evidence.into_iter().next().unwrap_or_default();
    (meaningful.remove(0), evidence)
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
    let mut used_param_names = HashSet::new();
    let json_params = ordered
        .iter()
        .enumerate()
        .map(|(idx, p)| {
            let fallback_idx = if p.arg_index == usize::MAX {
                idx
            } else {
                p.arg_index
            };
            InferredSignatureParam {
                name: normalize_inferred_param_name(&p.name, fallback_idx, &mut used_param_names),
                param_type: render_signature_type(&p.ty, ptr_bits),
            }
        })
        .collect::<Vec<_>>();
    let rendered_ret = render_signature_type(ret_type, ptr_bits);
    let (callconv, callconv_confidence) = compute_callconv_inference(arch_name, input_counts);
    let confidence = compute_signature_confidence(&ordered, ret_type, ret_evidence);
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

fn insert_known_signature_aliases(
    known: &mut HashMap<String, FunctionType>,
    name: &str,
    sig: &FunctionType,
) {
    if name.is_empty() {
        return;
    }
    known.insert(name.to_string(), sig.clone());

    for prefix in ["sym.imp.", "sym.", "imp.", "dbg.", "fcn."] {
        if let Some(stripped) = name.strip_prefix(prefix)
            && !stripped.is_empty()
        {
            known.insert(stripped.to_string(), sig.clone());
        }
    }
}

fn normalize_signature_registry_name(name: &str) -> Option<&'static str> {
    let normalized_owned = name.trim().to_ascii_lowercase();
    let mut normalized = normalized_owned.as_str();

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

    match normalized {
        "strlen" | "__strlen_chk" => Some("strlen"),
        "strcmp" => Some("strcmp"),
        "memcmp" => Some("memcmp"),
        "memcpy" | "__memcpy_chk" => Some("memcpy"),
        "memset" => Some("memset"),
        "malloc" | "__libc_malloc" | "__gi___libc_malloc" => Some("malloc"),
        "free" => Some("free"),
        "puts" => Some("puts"),
        "printf" | "__printf_chk" => Some("printf"),
        "exit" | "_exit" => Some("exit"),
        _ => None,
    }
}

pub fn enrich_known_function_signatures_from_names(
    type_facts: &mut FunctionTypeFacts,
    function_names: &HashMap<u64, String>,
    ptr_bits: u32,
) {
    let registry = SignatureRegistry::from_embedded_json();

    for name in function_names.values() {
        let mut candidates = vec![name.clone()];
        if let Some(sim_name) = normalize_signature_registry_name(name)
            && sim_name != name
            && !candidates.iter().any(|candidate| candidate == sim_name)
        {
            candidates.push(sim_name.to_string());
        }

        let resolved = candidates.into_iter().find_map(|candidate| {
            let mut arena = crate::TypeArena::default();
            registry
                .resolve(&candidate, &mut arena, ptr_bits)
                .map(|sig| {
                    (
                        candidate,
                        FunctionType {
                            return_type: crate::to_c_type_like(&arena, sig.ret),
                            params: sig
                                .params
                                .into_iter()
                                .map(|param| crate::to_c_type_like(&arena, param))
                                .collect(),
                            variadic: sig.variadic,
                        },
                    )
                })
        });

        let Some((resolved_name, sig)) = resolved else {
            continue;
        };

        insert_known_signature_aliases(&mut type_facts.known_function_signatures, name, &sig);
        if resolved_name != *name {
            insert_known_signature_aliases(
                &mut type_facts.known_function_signatures,
                &resolved_name,
                &sig,
            );
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
        arch
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
        let prepared = SsaArtifact::for_patterns(&[block], Some(&arch)).expect("prepared SSA");
        let pattern_blocks = prepared.local_ssa_blocks();

        let inferred = infer_signature_from_prepared_ssa(
            "narrow_return",
            "x86-64",
            64,
            &prepared,
            &pattern_blocks,
            &[],
            &BTreeSet::new(),
        );

        assert_eq!(inferred.ret_type, "uint32_t");
    }

    #[test]
    fn prepared_signature_does_not_type_void_return_from_program_counter() {
        let arch = x86_return_arch();
        let mut block = r2il::R2ILBlock::new(0x1000, 4);
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(8, 8),
        });
        let prepared = SsaArtifact::for_patterns(&[block], Some(&arch)).expect("prepared SSA");
        let pattern_blocks = prepared.local_ssa_blocks();

        let inferred = infer_signature_from_prepared_ssa(
            "void_return",
            "x86-64",
            64,
            &prepared,
            &pattern_blocks,
            &[],
            &BTreeSet::new(),
        );

        assert_eq!(inferred.ret_type, "void");
    }

    #[test]
    fn enrich_known_function_signatures_moves_registry_alias_policy_upstream() {
        let mut facts = FunctionTypeFacts::default();
        let names = HashMap::from([(0u64, "sym.imp.__printf_chk".to_string())]);

        enrich_known_function_signatures_from_names(&mut facts, &names, 64);

        assert!(
            facts
                .known_function_signatures
                .contains_key("sym.imp.__printf_chk")
        );
        assert!(facts.known_function_signatures.contains_key("__printf_chk"));
        assert!(facts.known_function_signatures.contains_key("printf"));
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
}
