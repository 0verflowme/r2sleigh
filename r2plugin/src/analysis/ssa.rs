use crate::blocks::BlockSlice;
use crate::context::require_ctx_view;
use crate::{
    ExportFormat, InstructionAction, InstructionExportInput, R2ILBlock, R2ILContext,
    SSA_JSON_SCHEMA_VERSION, SSAOpInfo, export_instruction, ssa_op_to_info,
};
use serde::Serialize;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::ptr;

/// Convert block to SSA and return JSON representation.
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2il_block_to_ssa_json(
    ctx: *const R2ILContext,
    block: *const R2ILBlock,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    if block.is_null() {
        return ptr::null_mut();
    }

    let blk = unsafe { &*block };
    let input = InstructionExportInput {
        disasm: ctx_view.disasm,
        arch: match ctx_view.arch {
            Some(arch) => arch,
            None => return ptr::null_mut(),
        },
        block: blk,
        addr: blk.addr,
        mnemonic: "",
        native_size: blk.size as usize,
    };

    match export_instruction(&input, InstructionAction::Ssa, ExportFormat::Json) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

/// Get def-use analysis for block as JSON.
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2il_block_defuse_json(
    ctx: *const R2ILContext,
    block: *const R2ILBlock,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    if block.is_null() {
        return ptr::null_mut();
    }

    let blk = unsafe { &*block };
    let input = InstructionExportInput {
        disasm: ctx_view.disasm,
        arch: match ctx_view.arch {
            Some(arch) => arch,
            None => return ptr::null_mut(),
        },
        block: blk,
        addr: blk.addr,
        mnemonic: "",
        native_size: blk.size as usize,
    };

    match export_instruction(&input, InstructionAction::Defuse, ExportFormat::Json) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[derive(Serialize)]
struct PhiNodeJson {
    dst: String,
    sources: Vec<(String, String)>,
}

#[derive(Serialize)]
struct SSABlockJson {
    addr: u64,
    addr_hex: String,
    size: u32,
    phis: Vec<PhiNodeJson>,
    ops: Vec<SSAOpInfo>,
}

#[derive(Serialize)]
struct SSAFunctionBodyJson {
    name: Option<String>,
    entry: u64,
    entry_hex: String,
    num_blocks: usize,
    blocks: Vec<SSABlockJson>,
}

#[derive(Serialize)]
struct PreparedFormalParameterJson {
    value: String,
    parameter: usize,
}

#[derive(Serialize)]
struct PreparedAddressTermJson {
    value_id: u32,
    value: String,
    coefficient: i64,
}

#[derive(Serialize)]
struct PreparedParameterAddressJson {
    value_id: u32,
    value: String,
    parameter: usize,
    terms: Vec<PreparedAddressTermJson>,
    offset: i64,
}

#[derive(Serialize)]
struct PreparedSsaFactsJson {
    formal_parameters: Vec<PreparedFormalParameterJson>,
    parameter_addresses: Vec<PreparedParameterAddressJson>,
}

#[derive(Serialize)]
struct PreparedSSAFunctionJson {
    schema_version: u32,
    #[serde(flatten)]
    function: SSAFunctionBodyJson,
    prepared: PreparedSsaFactsJson,
}

fn build_ssa_function_json(ssa_func: &r2ssa::SSAFunction) -> SSAFunctionBodyJson {
    let mut json_blocks = Vec::new();
    for &addr in ssa_func.block_addrs() {
        if let Some(block) = ssa_func.get_block(addr) {
            let phis = block
                .phis
                .iter()
                .map(|phi| PhiNodeJson {
                    dst: phi.dst.display_name(),
                    sources: phi
                        .sources
                        .iter()
                        .map(|(pred, var)| (format!("0x{:x}", pred), var.display_name()))
                        .collect(),
                })
                .collect();
            let ops = block.ops.iter().map(ssa_op_to_info).collect();
            json_blocks.push(SSABlockJson {
                addr,
                addr_hex: format!("0x{:x}", addr),
                size: block.size,
                phis,
                ops,
            });
        }
    }
    SSAFunctionBodyJson {
        name: ssa_func.name.clone(),
        entry: ssa_func.entry,
        entry_hex: format!("0x{:x}", ssa_func.entry),
        num_blocks: ssa_func.num_blocks(),
        blocks: json_blocks,
    }
}

fn prepared_ssa_function_json_string(artifact: &r2ssa::SsaArtifact) -> Option<String> {
    let graph = artifact.graph();
    let formal_parameters = artifact
        .function()
        .decompile_prep_facts()
        .into_iter()
        .flat_map(|facts| &facts.formal_parameters)
        .map(|(value, parameter)| PreparedFormalParameterJson {
            value: value.display_name(),
            parameter: *parameter,
        })
        .collect();
    let parameter_addresses = artifact
        .addresses()
        .parameter_expressions
        .iter()
        .map(|(value_id, expression)| {
            let value = graph.value(*value_id)?;
            Some(PreparedParameterAddressJson {
                value_id: value_id.0,
                value: value.var.display_name(),
                parameter: expression.parameter,
                terms: expression
                    .terms
                    .iter()
                    .map(|term| {
                        Some(PreparedAddressTermJson {
                            value_id: term.value.0,
                            value: graph.value(term.value)?.var.display_name(),
                            coefficient: term.coefficient,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
                offset: expression.offset,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    serde_json::to_string_pretty(&PreparedSSAFunctionJson {
        schema_version: SSA_JSON_SCHEMA_VERSION,
        function: build_ssa_function_json(artifact.function()),
        prepared: PreparedSsaFactsJson {
            formal_parameters,
            parameter_addresses,
        },
    })
    .ok()
}

/// Get function-level SSA as JSON (includes phi nodes).
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2ssa_function_json(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
) -> *mut c_char {
    if ctx.is_null() {
        return ptr::null_mut();
    }
    let Some(blocks) = (unsafe { BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return ptr::null_mut();
    };
    let ctx_ref = unsafe { &*ctx };

    let artifact = match r2ssa::SsaArtifact::for_decompile(blocks.as_slice(), ctx_ref.arch.as_ref())
    {
        Some(f) => f,
        None => return ptr::null_mut(),
    };
    let Some(json) = prepared_ssa_function_json_string(&artifact) else {
        return ptr::null_mut();
    };
    CString::new(json).map_or(ptr::null_mut(), |c| c.into_raw())
}

#[derive(Serialize)]
struct SSAOptStatsJson {
    iterations: usize,
    sccp_constants_found: usize,
    sccp_edges_pruned: usize,
    sccp_blocks_removed: usize,
    constants_propagated: usize,
    ops_simplified: usize,
    copies_propagated: usize,
    phis_simplified: usize,
    cse_replacements: usize,
    dce_removed_ops: usize,
    dce_removed_phis: usize,
}

#[derive(Serialize)]
struct SSAFunctionOptJson {
    schema_version: u32,
    optimized: bool,
    stats: SSAOptStatsJson,
    function: SSAFunctionBodyJson,
}

/// Get optimized function-level SSA as JSON (includes phi nodes).
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2ssa_function_opt_json(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
) -> *mut c_char {
    if ctx.is_null() {
        return ptr::null_mut();
    }
    let Some(blocks) = (unsafe { BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return ptr::null_mut();
    };
    let ctx_ref = unsafe { &*ctx };

    let mut ssa_func =
        match r2ssa::SSAFunction::from_blocks_raw(blocks.as_slice(), ctx_ref.arch.as_ref()) {
            Some(f) => f,
            None => return ptr::null_mut(),
        };
    let stats = ssa_func.optimize(&r2ssa::OptimizationConfig::default());
    let report = SSAFunctionOptJson {
        schema_version: SSA_JSON_SCHEMA_VERSION,
        optimized: true,
        stats: SSAOptStatsJson {
            iterations: stats.iterations,
            sccp_constants_found: stats.sccp_constants_found,
            sccp_edges_pruned: stats.sccp_edges_pruned,
            sccp_blocks_removed: stats.sccp_blocks_removed,
            constants_propagated: stats.constants_propagated,
            ops_simplified: stats.ops_simplified,
            copies_propagated: stats.copies_propagated,
            phis_simplified: stats.phis_simplified,
            cse_replacements: stats.cse_replacements,
            dce_removed_ops: stats.dce_removed_ops,
            dce_removed_phis: stats.dce_removed_phis,
        },
        function: build_ssa_function_json(&ssa_func),
    };

    match serde_json::to_string_pretty(&report) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[derive(Serialize)]
struct DefLocationJson {
    block: u64,
    block_hex: String,
    op_idx: usize,
}

#[derive(Serialize)]
struct UseLocationJson {
    block: u64,
    block_hex: String,
    op_idx: usize,
}

#[derive(Serialize)]
struct FunctionDefUseJson {
    definitions: std::collections::HashMap<String, DefLocationJson>,
    uses: std::collections::HashMap<String, Vec<UseLocationJson>>,
    live_in: std::collections::HashMap<String, Vec<String>>,
    live_out: std::collections::HashMap<String, Vec<String>>,
}

/// Get function-wide def-use analysis as JSON.
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2ssa_defuse_function_json(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
) -> *mut c_char {
    if ctx.is_null() {
        return ptr::null_mut();
    }
    let Some(blocks) = (unsafe { BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return ptr::null_mut();
    };
    let ctx_ref = unsafe { &*ctx };

    let ssa_func =
        match r2ssa::SSAFunction::from_blocks_with_arch(blocks.as_slice(), ctx_ref.arch.as_ref()) {
            Some(f) => f,
            None => return ptr::null_mut(),
        };

    let mut definitions = std::collections::HashMap::new();
    let mut uses: std::collections::HashMap<String, Vec<UseLocationJson>> =
        std::collections::HashMap::new();
    let mut live_in = std::collections::HashMap::new();
    let mut live_out = std::collections::HashMap::new();

    for &addr in ssa_func.block_addrs() {
        if let Some(block) = ssa_func.get_block(addr) {
            let block_hex = format!("0x{:x}", addr);
            let mut block_inputs = Vec::new();
            let mut block_outputs = Vec::new();
            let mut defined_in_block = std::collections::HashSet::new();

            for phi in &block.phis {
                let dst_name = phi.dst.display_name();
                definitions.insert(
                    dst_name.clone(),
                    DefLocationJson {
                        block: addr,
                        block_hex: block_hex.clone(),
                        op_idx: 0,
                    },
                );
                defined_in_block.insert(dst_name.clone());
                block_outputs.push(dst_name);
                for (_pred, src) in &phi.sources {
                    let src_name = src.display_name();
                    uses.entry(src_name.clone())
                        .or_default()
                        .push(UseLocationJson {
                            block: addr,
                            block_hex: block_hex.clone(),
                            op_idx: 0,
                        });
                }
            }

            for (op_idx, op) in block.ops.iter().enumerate() {
                if let Some(dst) = op.dst() {
                    let dst_name = dst.display_name();
                    definitions.insert(
                        dst_name.clone(),
                        DefLocationJson {
                            block: addr,
                            block_hex: block_hex.clone(),
                            op_idx: op_idx + 1,
                        },
                    );
                    defined_in_block.insert(dst_name.clone());
                    block_outputs.push(dst_name);
                }
                for src in op.sources() {
                    let src_name = src.display_name();
                    uses.entry(src_name.clone())
                        .or_default()
                        .push(UseLocationJson {
                            block: addr,
                            block_hex: block_hex.clone(),
                            op_idx: op_idx + 1,
                        });
                    if !defined_in_block.contains(&src_name) && !block_inputs.contains(&src_name) {
                        block_inputs.push(src_name);
                    }
                }
            }

            live_in.insert(block_hex.clone(), block_inputs);
            live_out.insert(block_hex, block_outputs);
        }
    }

    let json = FunctionDefUseJson {
        definitions,
        uses,
        live_in,
        live_out,
    };
    match serde_json::to_string_pretty(&json) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[derive(Serialize)]
struct DomTreeJson {
    entry: u64,
    entry_hex: String,
    idom: std::collections::HashMap<String, String>,
    children: std::collections::HashMap<String, Vec<String>>,
    dominance_frontier: std::collections::HashMap<String, Vec<String>>,
    depth: std::collections::HashMap<String, usize>,
}

/// Get dominator tree as JSON.
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2ssa_domtree_json(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
) -> *mut c_char {
    if ctx.is_null() {
        return ptr::null_mut();
    }
    let Some(blocks) = (unsafe { BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return ptr::null_mut();
    };
    let ctx_ref = unsafe { &*ctx };

    let ssa_func =
        match r2ssa::SSAFunction::from_blocks_with_arch(blocks.as_slice(), ctx_ref.arch.as_ref()) {
            Some(f) => f,
            None => return ptr::null_mut(),
        };
    let domtree = ssa_func.domtree();
    let mut idom_map = std::collections::HashMap::new();
    let mut children_map = std::collections::HashMap::new();
    let mut frontier_map = std::collections::HashMap::new();
    let mut depth_map = std::collections::HashMap::new();

    for &addr in ssa_func.block_addrs() {
        let block_hex = format!("0x{:x}", addr);
        if let Some(idom) = domtree.idom(addr) {
            idom_map.insert(block_hex.clone(), format!("0x{:x}", idom));
        }
        let children = domtree
            .children(addr)
            .iter()
            .map(|c| format!("0x{:x}", c))
            .collect();
        children_map.insert(block_hex.clone(), children);
        let frontier = domtree
            .frontier(addr)
            .map(|f| format!("0x{:x}", f))
            .collect();
        frontier_map.insert(block_hex.clone(), frontier);
        depth_map.insert(block_hex, domtree.depth(addr));
    }

    let json = DomTreeJson {
        entry: ssa_func.entry,
        entry_hex: format!("0x{:x}", ssa_func.entry),
        idom: idom_map,
        children: children_map,
        dominance_frontier: frontier_map,
        depth: depth_map,
    };
    match serde_json::to_string_pretty(&json) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[derive(Serialize)]
struct BackwardSliceJson {
    sink_var: String,
    ops: Vec<SliceOpJson>,
    blocks: Vec<String>,
}

#[derive(Serialize)]
struct SliceOpJson {
    #[serde(rename = "type")]
    op_type: String,
    block: String,
    index: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    op_str: Option<String>,
}

/// Compute backward slice from a variable name at a given block.
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2ssa_backward_slice_json(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    var_name: *const c_char,
) -> *mut c_char {
    if ctx.is_null() || var_name.is_null() {
        return ptr::null_mut();
    }
    let Some(blocks) = (unsafe { BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return ptr::null_mut();
    };
    let ctx_ref = unsafe { &*ctx };
    let var_name_str = match unsafe { CStr::from_ptr(var_name) }.to_str() {
        Ok(s) => s.to_string(),
        Err(_) => return ptr::null_mut(),
    };

    let ssa_func =
        match r2ssa::SSAFunction::from_blocks_with_arch(blocks.as_slice(), ctx_ref.arch.as_ref()) {
            Some(f) => f,
            None => return ptr::null_mut(),
        };

    let sink_var = {
        let mut found = None;
        'outer: for &addr in ssa_func.block_addrs() {
            if let Some(block) = ssa_func.get_block(addr) {
                for phi in &block.phis {
                    if phi.dst.display_name().eq_ignore_ascii_case(&var_name_str) {
                        found = Some(phi.dst.clone());
                        break 'outer;
                    }
                    for (_, src) in &phi.sources {
                        if src.display_name().eq_ignore_ascii_case(&var_name_str) {
                            found = Some(src.clone());
                            break 'outer;
                        }
                    }
                }
                for op in &block.ops {
                    if let Some(dst) = op.dst()
                        && dst.display_name().eq_ignore_ascii_case(&var_name_str)
                    {
                        found = Some(dst.clone());
                        break 'outer;
                    }
                    for src in op.sources() {
                        if src.display_name().eq_ignore_ascii_case(&var_name_str) {
                            found = Some(src.clone());
                            break 'outer;
                        }
                    }
                }
            }
        }
        match found {
            Some(v) => v,
            None => {
                let error_json = format!(r#"{{"error": "Variable '{}' not found"}}"#, var_name_str);
                return CString::new(error_json).map_or(ptr::null_mut(), |c| c.into_raw());
            }
        }
    };

    let slice = r2ssa::backward_slice_from_var(&ssa_func, &sink_var);
    let mut ops_json = Vec::new();
    for op_ref in &slice.ops {
        match op_ref {
            r2ssa::SliceOpRef::Phi {
                block_addr,
                phi_idx,
            } => {
                let op_str = ssa_func
                    .get_block(*block_addr)
                    .and_then(|block| block.phis.get(*phi_idx))
                    .map(|phi| format!("{} = phi(...)", phi.dst.display_name()));
                ops_json.push(SliceOpJson {
                    op_type: "phi".to_string(),
                    block: format!("0x{:x}", block_addr),
                    index: *phi_idx,
                    op_str,
                });
            }
            r2ssa::SliceOpRef::Op { block_addr, op_idx } => {
                let op_str = ssa_func
                    .get_block(*block_addr)
                    .and_then(|block| block.ops.get(*op_idx))
                    .map(|op| format!("{:?}", op));
                ops_json.push(SliceOpJson {
                    op_type: "op".to_string(),
                    block: format!("0x{:x}", block_addr),
                    index: *op_idx,
                    op_str,
                });
            }
        }
    }

    let blocks_hex = slice.blocks.iter().map(|b| format!("0x{:x}", b)).collect();
    let json = BackwardSliceJson {
        sink_var: var_name_str,
        ops: ops_json,
        blocks: blocks_hex,
    };
    match serde_json::to_string_pretty(&json) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn function_body_with_one_op() -> SSAFunctionBodyJson {
        let op = r2ssa::SSAOp::Copy {
            dst: r2ssa::SSAVar::new("dst", 1, 8),
            src: r2ssa::SSAVar::new("src", 1, 8),
        };
        SSAFunctionBodyJson {
            name: Some("test".to_string()),
            entry: 0x1000,
            entry_hex: "0x1000".to_string(),
            num_blocks: 1,
            blocks: vec![SSABlockJson {
                addr: 0x1000,
                addr_hex: "0x1000".to_string(),
                size: 1,
                phis: Vec::new(),
                ops: vec![ssa_op_to_info(&op)],
            }],
        }
    }

    #[test]
    fn prepared_ssa_document_versions_operations_once() {
        let value = serde_json::to_value(PreparedSSAFunctionJson {
            schema_version: SSA_JSON_SCHEMA_VERSION,
            function: function_body_with_one_op(),
            prepared: PreparedSsaFactsJson {
                formal_parameters: Vec::new(),
                parameter_addresses: Vec::new(),
            },
        })
        .expect("prepared SSA JSON");

        assert_eq!(value["schema_version"], SSA_JSON_SCHEMA_VERSION);
        assert!(value["blocks"][0]["ops"][0].get("schema_version").is_none());
    }

    #[test]
    fn optimized_ssa_document_carries_current_schema() {
        let value = serde_json::to_value(SSAFunctionOptJson {
            schema_version: SSA_JSON_SCHEMA_VERSION,
            optimized: true,
            stats: SSAOptStatsJson {
                iterations: 0,
                sccp_constants_found: 0,
                sccp_edges_pruned: 0,
                sccp_blocks_removed: 0,
                constants_propagated: 0,
                ops_simplified: 0,
                copies_propagated: 0,
                phis_simplified: 0,
                cse_replacements: 0,
                dce_removed_ops: 0,
                dce_removed_phis: 0,
            },
            function: function_body_with_one_op(),
        })
        .expect("optimized SSA JSON");

        assert_eq!(value["schema_version"], SSA_JSON_SCHEMA_VERSION);
        assert!(
            value["function"]["blocks"][0]["ops"][0]
                .get("schema_version")
                .is_none()
        );
    }
}
