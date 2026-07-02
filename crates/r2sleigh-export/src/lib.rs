//! Unified instruction export pipeline for r2sleigh.

use r2il::{ArchSpec, R2ILBlock, R2ILOp, SpaceId, Varnode, validate_block_full};
use r2sleigh_lift::{Disassembler, format_op, op_to_esil_named};
use serde::Serialize;
use serde_json::Value;
use std::collections::HashSet;
use std::fmt;
use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstructionAction {
    Lift,
    Ssa,
    Defuse,
    Dec,
}

impl InstructionAction {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Lift => "lift",
            Self::Ssa => "ssa",
            Self::Defuse => "defuse",
            Self::Dec => "dec",
        }
    }
}

impl fmt::Display for InstructionAction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExportFormat {
    Json,
    Text,
    Esil,
    CLike,
    R2Cmd,
}

impl ExportFormat {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Json => "json",
            Self::Text => "text",
            Self::Esil => "esil",
            Self::CLike => "c_like",
            Self::R2Cmd => "r2cmd",
        }
    }
}

impl fmt::Display for ExportFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

pub struct InstructionExportInput<'a> {
    pub disasm: &'a Disassembler,
    pub arch: &'a ArchSpec,
    pub block: &'a R2ILBlock,
    pub addr: u64,
    pub mnemonic: &'a str,
    pub native_size: usize,
}

#[derive(Debug, Error)]
pub enum ExportError {
    #[error(
        "unsupported action/format combination: action={action} format={format}. Supported formats for {action}: {supported}"
    )]
    UnsupportedCombination {
        action: InstructionAction,
        format: ExportFormat,
        supported: String,
    },
    #[error("validation failed: {0}")]
    ValidationFailed(String),
    #[error("serialization failed: {0}")]
    SerializeError(String),
    #[error("render failed: {0}")]
    RenderError(String),
}

pub fn export_instruction(
    input: &InstructionExportInput<'_>,
    action: InstructionAction,
    format: ExportFormat,
) -> Result<String, ExportError> {
    validate_block_full(input.block, input.arch)
        .map_err(|e| ExportError::ValidationFailed(e.to_string()))?;
    ensure_supported(action, format)?;

    match action {
        InstructionAction::Lift => export_lift(input, format),
        InstructionAction::Ssa => export_ssa(input, format),
        InstructionAction::Defuse => export_defuse(input, format),
        InstructionAction::Dec => export_dec_action(input, format),
    }
}

pub fn op_json_named(disasm: &Disassembler, op: &R2ILOp) -> Result<String, ExportError> {
    let mut value =
        serde_json::to_value(op).map_err(|e| ExportError::SerializeError(e.to_string()))?;
    annotate_register_names(&mut value, disasm);
    annotate_userop_names(&mut value, disasm);
    serde_json::to_string(&value).map_err(|e| ExportError::SerializeError(e.to_string()))
}

fn ensure_supported(action: InstructionAction, format: ExportFormat) -> Result<(), ExportError> {
    let supported = supported_formats(action);
    if supported.contains(&format) {
        return Ok(());
    }
    let supported = supported
        .iter()
        .map(|f| f.as_str())
        .collect::<Vec<_>>()
        .join(", ");
    Err(ExportError::UnsupportedCombination {
        action,
        format,
        supported,
    })
}

fn supported_formats(action: InstructionAction) -> &'static [ExportFormat] {
    use ExportFormat::*;
    match action {
        InstructionAction::Lift => &[Json, Text, Esil, R2Cmd],
        InstructionAction::Ssa => &[Json, Text],
        InstructionAction::Defuse => &[Json, Text],
        InstructionAction::Dec => {
            #[cfg(feature = "dec")]
            {
                &[CLike, Json, Text]
            }
            #[cfg(not(feature = "dec"))]
            {
                &[]
            }
        }
    }
}

fn export_lift(
    input: &InstructionExportInput<'_>,
    format: ExportFormat,
) -> Result<String, ExportError> {
    match format {
        ExportFormat::Json => {
            let value = lift_json_value(input)?;
            serde_json::to_string_pretty(&value)
                .map_err(|e| ExportError::SerializeError(e.to_string()))
        }
        ExportFormat::Text => {
            let mut out = format!(
                "0x{:x}  {}  (size={})\nP-code ({} ops):",
                input.addr,
                input.mnemonic,
                input.native_size,
                input.block.ops.len()
            );
            for (i, op) in input.block.ops.iter().enumerate() {
                out.push_str(&format!("\n  {}: {}", i, format_op(input.disasm, op)));
            }
            Ok(out)
        }
        ExportFormat::Esil => {
            let lines = input
                .block
                .ops
                .iter()
                .map(|op| op_to_esil_named(input.disasm, op))
                .collect::<Vec<_>>();
            Ok(lines.join("\n"))
        }
        ExportFormat::R2Cmd => {
            let mut out = Vec::new();
            for (idx, op) in input.block.ops.iter().enumerate() {
                let op_json = op_json_named(input.disasm, op)?;
                let op_value: Value = serde_json::from_str(&op_json)
                    .map_err(|e| ExportError::SerializeError(e.to_string()))?;

                let op_name =
                    op_name_from_value(&op_value).unwrap_or_else(|| "unknown".to_string());
                let mut sidecar = serde_json::Map::new();
                sidecar.insert("op_index".to_string(), serde_json::json!(idx));
                sidecar.insert("op".to_string(), Value::String(op_name));
                sidecar.insert("op_json".to_string(), op_value);
                if let Some(meta) = input.block.op_metadata.get(&idx) {
                    sidecar.insert(
                        "meta".to_string(),
                        serde_json::to_value(meta)
                            .map_err(|e| ExportError::SerializeError(e.to_string()))?,
                    );
                }
                out.push(format!("# {}", Value::Object(sidecar)));
                out.push(format!("ae {}", op_to_esil_named(input.disasm, op)));
            }
            Ok(out.join("\n"))
        }
        ExportFormat::CLike => Err(ExportError::UnsupportedCombination {
            action: InstructionAction::Lift,
            format,
            supported: "json, text, esil, r2cmd".to_string(),
        }),
    }
}

fn lift_json_value(input: &InstructionExportInput<'_>) -> Result<Value, ExportError> {
    let mut ops = Vec::new();
    for op in &input.block.ops {
        let op_json = op_json_named(input.disasm, op)?;
        let op_value: Value = serde_json::from_str(&op_json)
            .map_err(|e| ExportError::SerializeError(e.to_string()))?;
        ops.push(op_value);
    }

    let mut out = serde_json::json!({
        "addr": format!("0x{:x}", input.block.addr),
        "size": input.native_size,
        "mnemonic": input.mnemonic,
        "ops": ops,
    });
    if !input.block.op_metadata.is_empty() {
        out["op_metadata"] = serde_json::to_value(&input.block.op_metadata)
            .map_err(|e| ExportError::SerializeError(e.to_string()))?;
    }
    Ok(out)
}

fn export_ssa(
    input: &InstructionExportInput<'_>,
    format: ExportFormat,
) -> Result<String, ExportError> {
    let ssa_block = r2ssa::block::to_ssa(input.block, input.disasm);
    let ops_info: Vec<SSAOpInfo> = ssa_block.ops.iter().map(ssa_op_to_info).collect();

    match format {
        ExportFormat::Json => serde_json::to_string_pretty(&ops_info)
            .map_err(|e| ExportError::SerializeError(e.to_string())),
        ExportFormat::Text => {
            let mut lines = Vec::new();
            for (idx, info) in ops_info.iter().enumerate() {
                let dst = info.dst.as_deref().unwrap_or("-");
                let sources = if info.sources.is_empty() {
                    String::new()
                } else {
                    info.sources.join(", ")
                };
                lines.push(format!(
                    "{}: {} dst={} src=[{}]",
                    idx, info.op, dst, sources
                ));
            }
            Ok(lines.join("\n"))
        }
        _ => Err(ExportError::UnsupportedCombination {
            action: InstructionAction::Ssa,
            format,
            supported: "json, text".to_string(),
        }),
    }
}

fn export_defuse(
    input: &InstructionExportInput<'_>,
    format: ExportFormat,
) -> Result<String, ExportError> {
    let ssa_block = r2ssa::block::to_ssa(input.block, input.disasm);
    let info = r2ssa::def_use(&ssa_block);
    let json_info = DefUseInfoJson {
        inputs: sorted_set(&info.inputs),
        outputs: sorted_set(&info.outputs),
        live: sorted_set(&info.live),
    };

    match format {
        ExportFormat::Json => serde_json::to_string_pretty(&json_info)
            .map_err(|e| ExportError::SerializeError(e.to_string())),
        ExportFormat::Text => Ok(format!(
            "inputs: {}\noutputs: {}\nlive: {}",
            json_info.inputs.join(", "),
            json_info.outputs.join(", "),
            json_info.live.join(", ")
        )),
        _ => Err(ExportError::UnsupportedCombination {
            action: InstructionAction::Defuse,
            format,
            supported: "json, text".to_string(),
        }),
    }
}

fn export_dec_action(
    input: &InstructionExportInput<'_>,
    format: ExportFormat,
) -> Result<String, ExportError> {
    #[cfg(feature = "dec")]
    {
        export_dec(input, format)
    }
    #[cfg(not(feature = "dec"))]
    {
        let _ = input;
        Err(ExportError::UnsupportedCombination {
            action: InstructionAction::Dec,
            format,
            supported: String::new(),
        })
    }
}

#[cfg(feature = "dec")]
fn export_dec(
    input: &InstructionExportInput<'_>,
    format: ExportFormat,
) -> Result<String, ExportError> {
    let ssa_block = r2ssa::block::to_ssa(input.block, input.disasm);
    let residuals = ssa_block
        .ops
        .iter()
        .enumerate()
        .map(|(op_index, op)| DecResidualJson {
            kind: "residual",
            op_index,
            comment: format!(
                "r2sleigh-export residual: instruction-level dec requires r2engine FunctionFacts render proof; executable C suppressed: {op:?}"
            ),
        })
        .collect::<Vec<_>>();

    match format {
        ExportFormat::Json => serde_json::to_string_pretty(&residuals)
            .map_err(|e| ExportError::SerializeError(e.to_string())),
        ExportFormat::Text | ExportFormat::CLike => Ok(residuals
            .iter()
            .map(|residual| format!("/* {} */", residual.comment))
            .collect::<Vec<_>>()
            .join("\n")),
        _ => Err(ExportError::UnsupportedCombination {
            action: InstructionAction::Dec,
            format,
            supported: "c_like, json, text".to_string(),
        }),
    }
}

fn sorted_set(values: &HashSet<String>) -> Vec<String> {
    let mut out: Vec<String> = values.iter().cloned().collect();
    out.sort();
    out
}

fn annotate_register_names(value: &mut Value, disasm: &Disassembler) {
    match value {
        Value::Object(map) => {
            let is_varnode =
                map.contains_key("space") && map.contains_key("offset") && map.contains_key("size");
            if is_varnode {
                let space = map.get("space").and_then(Value::as_str);
                if let Some(space_str) = space
                    && space_str.eq_ignore_ascii_case("register")
                {
                    let offset = map.get("offset").and_then(Value::as_u64);
                    let size = map.get("size").and_then(Value::as_u64);
                    if let (Some(offset), Some(size)) = (offset, size)
                        && let Ok(size32) = u32::try_from(size)
                    {
                        let vn = Varnode {
                            space: SpaceId::Register,
                            offset,
                            size: size32,
                            meta: None,
                        };
                        if let Some(name) = disasm.register_name(&vn) {
                            map.insert("name".to_string(), Value::String(name));
                        }
                    }
                }
            }

            for value in map.values_mut() {
                annotate_register_names(value, disasm);
            }
        }
        Value::Array(items) => {
            for item in items.iter_mut() {
                annotate_register_names(item, disasm);
            }
        }
        _ => {}
    }
}

fn annotate_userop_names(value: &mut Value, disasm: &Disassembler) {
    match value {
        Value::Object(map) => {
            if let Some(callother) = map.get_mut("CallOther")
                && let Value::Object(call_map) = callother
            {
                let userop = call_map.get("userop").and_then(Value::as_u64);
                if let Some(userop) = userop
                    && let Some(name) = disasm.userop_name(userop as u32)
                {
                    call_map.insert("userop_name".to_string(), Value::String(name.to_string()));
                }
            }

            for value in map.values_mut() {
                annotate_userop_names(value, disasm);
            }
        }
        Value::Array(items) => {
            for item in items.iter_mut() {
                annotate_userop_names(item, disasm);
            }
        }
        _ => {}
    }
}

fn op_name_from_value(value: &Value) -> Option<String> {
    let map = value.as_object()?;
    map.keys().next().cloned()
}

#[derive(Serialize)]
struct SSAOpInfo {
    op: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    dst: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    sources: Vec<String>,
}

fn ssa_op_to_info(op: &r2ssa::SSAOp) -> SSAOpInfo {
    let op_name = serde_json::to_value(op)
        .ok()
        .and_then(|v| op_name_from_value(&v))
        .unwrap_or_else(|| "Unknown".to_string());
    SSAOpInfo {
        op: op_name,
        dst: op.dst().map(|v| v.display_name()),
        sources: op.sources().iter().map(|v| v.display_name()).collect(),
    }
}

#[derive(Serialize)]
struct DefUseInfoJson {
    inputs: Vec<String>,
    outputs: Vec<String>,
    live: Vec<String>,
}

#[cfg(feature = "dec")]
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct DecResidualJson {
    kind: &'static str,
    op_index: usize,
    comment: String,
}

#[cfg(all(test, feature = "x86"))]
mod tests {
    use super::*;
    use r2il::{MemoryClass, OpMetadata, ScalarKind, VarnodeMetadata};
    use r2sleigh_lift::{build_arch_spec, userop_map_for_arch};
    use std::collections::BTreeMap;

    const X86_BYTES_MINIMAL: &str = "4889c000000000000000000000000000";
    #[cfg(feature = "dec")]
    const X86_BYTES_DEC: &str = "48ffc000000000000000000000000000";

    fn x86_disasm_and_spec() -> (Disassembler, ArchSpec) {
        let spec = build_arch_spec(
            sleigh_config::processor_x86::SLA_X86_64,
            sleigh_config::processor_x86::PSPEC_X86_64,
            "x86-64",
        )
        .expect("arch spec");
        let mut disasm = Disassembler::from_sla(
            sleigh_config::processor_x86::SLA_X86_64,
            sleigh_config::processor_x86::PSPEC_X86_64,
            "x86-64",
        )
        .expect("disasm");
        disasm.set_userop_map(userop_map_for_arch("x86-64"));
        (disasm, spec)
    }

    fn lift_input(bytes_hex: &str, addr: u64) -> InstructionExportInput<'static> {
        let (disasm, spec) = x86_disasm_and_spec();
        let bytes = hex::decode(bytes_hex).expect("hex");
        let block = disasm.lift(&bytes, addr).expect("lift");
        let (mnemonic, native_size) = disasm.disasm_native(&bytes, addr).expect("disasm");

        let disasm = Box::leak(Box::new(disasm));
        let spec = Box::leak(Box::new(spec));
        let block = Box::leak(Box::new(block));
        let mnemonic = Box::leak(Box::new(mnemonic));

        InstructionExportInput {
            disasm,
            arch: spec,
            block,
            addr,
            mnemonic,
            native_size,
        }
    }

    fn canonicalize_json(value: &Value) -> Value {
        match value {
            Value::Object(map) => {
                let mut sorted = BTreeMap::new();
                for (k, v) in map {
                    sorted.insert(k.clone(), canonicalize_json(v));
                }
                let mut out = serde_json::Map::new();
                for (k, v) in sorted {
                    out.insert(k, v);
                }
                Value::Object(out)
            }
            Value::Array(items) => Value::Array(items.iter().map(canonicalize_json).collect()),
            _ => value.clone(),
        }
    }

    fn normalize_json_output(output: &str) -> String {
        let parsed: Value = serde_json::from_str(output.trim()).expect("json");
        canonicalize_json(&parsed).to_string()
    }

    fn normalize_text_output(output: &str) -> String {
        let text = output.replace("\r\n", "\n");
        let mut lines: Vec<String> = text.lines().map(|l| l.trim_end().to_string()).collect();
        while lines.last().is_some_and(|l| l.is_empty()) {
            lines.pop();
        }
        lines.join("\n")
    }

    #[cfg(feature = "dec")]
    fn normalize_c_like_output(output: &str) -> String {
        let text = output.replace("\r\n", "\n");
        let mut lines = Vec::new();
        let mut prev_blank = false;
        for raw_line in text.lines() {
            let line = raw_line.trim_end();
            let blank = line.is_empty();
            if blank && prev_blank {
                continue;
            }
            lines.push(line.to_string());
            prev_blank = blank;
        }
        while lines.first().is_some_and(|l| l.is_empty()) {
            lines.remove(0);
        }
        while lines.last().is_some_and(|l| l.is_empty()) {
            lines.pop();
        }
        lines.join("\n")
    }

    fn normalize_r2cmd_output(output: &str) -> String {
        let text = output.replace("\r\n", "\n");
        let lines: Vec<&str> = text.lines().collect();
        assert!(!lines.is_empty(), "r2cmd output must not be empty");
        assert_eq!(lines.len() % 2, 0, "r2cmd output must be line-paired");
        let mut normalized = Vec::new();
        for (idx, line) in lines.iter().enumerate() {
            let line = line.trim_end();
            if idx % 2 == 0 {
                assert!(line.starts_with("# "), "expected sidecar at index {}", idx);
                let sidecar: Value =
                    serde_json::from_str(line.trim_start_matches("# ")).expect("sidecar json");
                normalized.push(format!("# {}", canonicalize_json(&sidecar)));
            } else {
                assert!(line.starts_with("ae "), "expected ae line at index {}", idx);
                normalized.push(line.to_string());
            }
        }
        normalized.join("\n")
    }

    fn assert_export_deterministic(
        bytes_hex: &str,
        action: InstructionAction,
        format: ExportFormat,
        normalizer: fn(&str) -> String,
    ) -> String {
        let input1 = lift_input(bytes_hex, 0x1000);
        let out1 = export_instruction(&input1, action, format).expect("first export");
        let input2 = lift_input(bytes_hex, 0x1000);
        let out2 = export_instruction(&input2, action, format).expect("second export");
        let norm1 = normalizer(&out1);
        let norm2 = normalizer(&out2);
        assert_eq!(
            norm1, norm2,
            "non-deterministic export for action={}, format={}",
            action, format
        );
        norm1
    }

    #[test]
    fn lift_json_includes_op_and_varnode_metadata() {
        let (disasm, spec) = x86_disasm_and_spec();
        let mut block = R2ILBlock::new(0x1000, 1);
        let vn_meta = VarnodeMetadata {
            scalar_kind: Some(ScalarKind::UnsignedInt),
            ..Default::default()
        };
        block.push_with_metadata(
            R2ILOp::Copy {
                dst: Varnode::register(0, 8).with_meta(vn_meta),
                src: Varnode::constant(1, 8),
            },
            Some(OpMetadata {
                instruction_addr: None,
                memory_class: Some(MemoryClass::Stack),
                endianness: None,
                memory_ordering: None,
                permissions: None,
                valid_range: None,
                bank_id: None,
                segment_id: None,
                atomic_kind: None,
            }),
        );
        let input = InstructionExportInput {
            disasm: &disasm,
            arch: &spec,
            block: &block,
            addr: 0x1000,
            mnemonic: "mov",
            native_size: 1,
        };

        let out = export_instruction(&input, InstructionAction::Lift, ExportFormat::Json)
            .expect("lift json");
        let parsed: Value = serde_json::from_str(&out).expect("json");

        assert!(parsed.get("op_metadata").is_some(), "expected op metadata");
        assert!(
            parsed.to_string().contains("\"meta\""),
            "expected varnode metadata in output: {}",
            parsed
        );
    }

    #[test]
    fn lift_r2cmd_emits_comment_then_ae_per_op() {
        let input = lift_input(X86_BYTES_MINIMAL, 0x1000);
        let out = export_instruction(&input, InstructionAction::Lift, ExportFormat::R2Cmd)
            .expect("lift r2cmd");
        let lines: Vec<&str> = out.lines().collect();
        assert!(!lines.is_empty(), "expected output lines");
        assert!(
            lines[0].starts_with("# "),
            "first line must be sidecar comment"
        );
        assert!(
            lines.get(1).is_some_and(|l| l.starts_with("ae ")),
            "second line must be an ae replay line"
        );
    }

    #[test]
    fn ssa_json_is_valid_and_nonempty() {
        let input = lift_input(X86_BYTES_MINIMAL, 0x1000);
        let out = export_instruction(&input, InstructionAction::Ssa, ExportFormat::Json)
            .expect("ssa json");
        let parsed: Value = serde_json::from_str(&out).expect("json");
        let arr = parsed.as_array().expect("array");
        assert!(!arr.is_empty(), "expected non-empty ssa ops");
    }

    #[test]
    fn defuse_json_contains_inputs_outputs_live() {
        let input = lift_input(X86_BYTES_MINIMAL, 0x1000);
        let out = export_instruction(&input, InstructionAction::Defuse, ExportFormat::Json)
            .expect("defuse json");
        let parsed: Value = serde_json::from_str(&out).expect("json");
        assert!(parsed.get("inputs").is_some());
        assert!(parsed.get("outputs").is_some());
        assert!(parsed.get("live").is_some());
    }

    #[test]
    #[cfg(feature = "dec")]
    fn dec_c_like_residualizes_without_function_facts() {
        let input = lift_input(X86_BYTES_DEC, 0x1000);
        let out = export_instruction(&input, InstructionAction::Dec, ExportFormat::CLike)
            .expect("dec residual");
        assert!(
            out.contains("r2sleigh-export residual")
                && out.contains("FunctionFacts render proof")
                && out.contains("executable C suppressed"),
            "expected explicit residual, got: {out}"
        );
        assert!(
            out.lines()
                .all(|line| line.starts_with("/* ") && line.ends_with(" */")),
            "instruction-level dec must stay comment-only: {out}"
        );
    }

    #[test]
    fn unsupported_combo_returns_error() {
        let input = lift_input(X86_BYTES_MINIMAL, 0x1000);
        let err = export_instruction(&input, InstructionAction::Ssa, ExportFormat::Esil)
            .expect_err("unsupported combo must fail");
        assert!(
            matches!(err, ExportError::UnsupportedCombination { .. }),
            "unexpected error kind: {}",
            err
        );
    }

    #[test]
    fn ensure_supported_enforces_action_format_matrix() {
        ensure_supported(InstructionAction::Lift, ExportFormat::Json)
            .expect("lift json should be supported");
        ensure_supported(InstructionAction::Defuse, ExportFormat::Text)
            .expect("defuse text should be supported");

        let err = ensure_supported(InstructionAction::Lift, ExportFormat::CLike)
            .expect_err("lift must not accept c_like format");
        assert!(
            matches!(
                err,
                ExportError::UnsupportedCombination {
                    action: InstructionAction::Lift,
                    format: ExportFormat::CLike,
                    ..
                }
            ),
            "unexpected support error kind: {}",
            err
        );
    }

    #[test]
    #[cfg(not(feature = "dec"))]
    fn dec_action_is_typed_but_unsupported_without_dec_feature() {
        let input = lift_input(X86_BYTES_MINIMAL, 0x1000);
        let err = export_instruction(&input, InstructionAction::Dec, ExportFormat::CLike)
            .expect_err("dec export must be feature-gated");
        assert!(
            matches!(
                err,
                ExportError::UnsupportedCombination {
                    action: InstructionAction::Dec,
                    format: ExportFormat::CLike,
                    ..
                }
            ),
            "unexpected error kind: {}",
            err
        );
    }

    #[test]
    #[cfg(not(feature = "dec"))]
    fn dec_feature_gate_rejects_at_support_and_execution_layers() {
        let input = lift_input(X86_BYTES_MINIMAL, 0x1000);

        assert!(
            supported_formats(InstructionAction::Dec).is_empty(),
            "dec must advertise no supported formats without the dec feature"
        );

        let support_err = ensure_supported(InstructionAction::Dec, ExportFormat::CLike)
            .expect_err("dec support must be disabled without the dec feature");
        assert!(
            matches!(
                support_err,
                ExportError::UnsupportedCombination {
                    action: InstructionAction::Dec,
                    format: ExportFormat::CLike,
                    ..
                }
            ),
            "unexpected support error kind: {}",
            support_err
        );

        let execution_err = export_dec_action(&input, ExportFormat::CLike)
            .expect_err("dec execution must be disabled without the dec feature");
        assert!(
            matches!(
                execution_err,
                ExportError::UnsupportedCombination {
                    action: InstructionAction::Dec,
                    format: ExportFormat::CLike,
                    ..
                }
            ),
            "unexpected execution error kind: {}",
            execution_err
        );
    }

    #[test]
    fn validation_failure_propagates() {
        let (disasm, arch) = x86_disasm_and_spec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::register(8, 4),
        });

        let input = InstructionExportInput {
            disasm: &disasm,
            arch: &arch,
            block: &block,
            addr: 0x1000,
            mnemonic: "copy",
            native_size: 1,
        };

        let err = export_instruction(&input, InstructionAction::Lift, ExportFormat::Json)
            .expect_err("invalid block must fail");
        assert!(
            matches!(err, ExportError::ValidationFailed(_)),
            "unexpected error kind: {}",
            err
        );
    }

    #[test]
    fn deterministic_matrix_for_supported_pairs() {
        for format in [
            ExportFormat::Json,
            ExportFormat::Text,
            ExportFormat::Esil,
            ExportFormat::R2Cmd,
        ] {
            let normalized = assert_export_deterministic(
                X86_BYTES_MINIMAL,
                InstructionAction::Lift,
                format,
                match format {
                    ExportFormat::Json => normalize_json_output,
                    ExportFormat::Text | ExportFormat::Esil => normalize_text_output,
                    ExportFormat::R2Cmd => normalize_r2cmd_output,
                    ExportFormat::CLike => unreachable!("not in lift matrix"),
                },
            );
            assert!(
                !normalized.trim().is_empty(),
                "lift output should be non-empty"
            );
        }

        for format in [ExportFormat::Json, ExportFormat::Text] {
            let normalized = assert_export_deterministic(
                X86_BYTES_MINIMAL,
                InstructionAction::Ssa,
                format,
                match format {
                    ExportFormat::Json => normalize_json_output,
                    ExportFormat::Text => normalize_text_output,
                    _ => unreachable!("ssa supports json/text"),
                },
            );
            assert!(
                !normalized.trim().is_empty(),
                "ssa output should be non-empty"
            );
        }

        for format in [ExportFormat::Json, ExportFormat::Text] {
            let normalized = assert_export_deterministic(
                X86_BYTES_MINIMAL,
                InstructionAction::Defuse,
                format,
                match format {
                    ExportFormat::Json => normalize_json_output,
                    ExportFormat::Text => normalize_text_output,
                    _ => unreachable!("defuse supports json/text"),
                },
            );
            assert!(
                !normalized.trim().is_empty(),
                "defuse output should be non-empty"
            );
        }

        #[cfg(feature = "dec")]
        {
            for format in [ExportFormat::CLike, ExportFormat::Json, ExportFormat::Text] {
                let normalized = assert_export_deterministic(
                    X86_BYTES_DEC,
                    InstructionAction::Dec,
                    format,
                    match format {
                        ExportFormat::CLike => normalize_c_like_output,
                        ExportFormat::Json => normalize_json_output,
                        ExportFormat::Text => normalize_text_output,
                        _ => unreachable!("dec supports c_like/json/text"),
                    },
                );
                assert!(
                    !normalized.trim().is_empty(),
                    "dec output should be non-empty"
                );
            }
        }
    }

    #[test]
    fn compact_fixture_expected_literals_stay_stable() {
        let lift_text = assert_export_deterministic(
            X86_BYTES_MINIMAL,
            InstructionAction::Lift,
            ExportFormat::Text,
            normalize_text_output,
        );
        assert_eq!(
            lift_text,
            "0x1000  MOV RAX,RAX  (size=3)\nP-code (1 ops):\n  0: Copy { dst: RAX, src: RAX }"
        );

        let lift_esil = assert_export_deterministic(
            X86_BYTES_MINIMAL,
            InstructionAction::Lift,
            ExportFormat::Esil,
            normalize_text_output,
        );
        assert_eq!(lift_esil, "rax,rax,=");

        let lift_r2cmd = assert_export_deterministic(
            X86_BYTES_MINIMAL,
            InstructionAction::Lift,
            ExportFormat::R2Cmd,
            normalize_r2cmd_output,
        );
        assert_eq!(
            lift_r2cmd,
            "# {\"op\":\"Copy\",\"op_index\":0,\"op_json\":{\"Copy\":{\"dst\":{\"meta\":{\"storage_class\":\"register\"},\"name\":\"RAX\",\"offset\":0,\"size\":8,\"space\":\"Register\"},\"src\":{\"meta\":{\"storage_class\":\"register\"},\"name\":\"RAX\",\"offset\":0,\"size\":8,\"space\":\"Register\"}}}}\nae rax,rax,="
        );

        let ssa_text = assert_export_deterministic(
            X86_BYTES_MINIMAL,
            InstructionAction::Ssa,
            ExportFormat::Text,
            normalize_text_output,
        );
        assert_eq!(ssa_text, "0: Copy dst=RAX_1 src=[RAX_1]");

        let defuse_json = assert_export_deterministic(
            X86_BYTES_MINIMAL,
            InstructionAction::Defuse,
            ExportFormat::Json,
            normalize_json_output,
        );
        assert_eq!(
            defuse_json,
            "{\"inputs\":[],\"live\":[\"RAX_1\"],\"outputs\":[]}"
        );

        #[cfg(feature = "dec")]
        {
            let dec_json = assert_export_deterministic(
                X86_BYTES_MINIMAL,
                InstructionAction::Dec,
                ExportFormat::Json,
                normalize_json_output,
            );
            assert!(
                dec_json.contains("\"kind\":\"residual\"")
                    && dec_json.contains("FunctionFacts render proof")
                    && dec_json.contains("executable C suppressed"),
                "dec json must be explicit residual-only output: {dec_json}"
            );
        }
    }
}
