use crate::blocks::BlockSlice;
use crate::context::require_ctx_view;
use crate::{R2ILBlock, R2ILContext, R2ILOp};
use serde::Serialize;
use std::ffi::CString;
use std::ptr;

/// Generate ASCII CFG for a function.
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2cfg_function_ascii(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
) -> *mut std::os::raw::c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    let Some(blocks) = (unsafe { BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return ptr::null_mut();
    };

    let cfg = match r2ssa::CFG::from_blocks(blocks.as_slice()) {
        Some(cfg) => cfg,
        None => return ptr::null_mut(),
    };
    let output = render_cfg_ascii(&cfg, ctx_view.disasm);
    CString::new(output).map_or(ptr::null_mut(), |c| c.into_raw())
}

fn render_cfg_ascii(cfg: &r2ssa::CFG, disasm: &r2sleigh_lift::Disassembler) -> String {
    use std::fmt::Write;

    let mut output = String::new();
    let block_addrs = cfg.reverse_postorder();
    if block_addrs.is_empty() {
        return "Empty CFG\n".to_string();
    }

    for addr in &block_addrs {
        if let Some(block) = cfg.get_block(*addr) {
            let is_entry = cfg.entry == *addr;
            let entry_marker = if is_entry { " [entry]" } else { "" };
            let _ = writeln!(
                output,
                "┌─────────────────────────────────────────────────┐"
            );
            let _ = writeln!(output, "│ 0x{:x}{:<30} │", addr, entry_marker);
            let _ = writeln!(
                output,
                "├─────────────────────────────────────────────────┤"
            );

            let ops_to_show = std::cmp::min(5, block.ops.len());
            for op in block.ops.iter().take(ops_to_show) {
                let op_str = format_r2il_op_short(op, disasm);
                let truncated = if op_str.len() > 45 {
                    format!("{}...", &op_str[..42])
                } else {
                    op_str
                };
                let _ = writeln!(output, "│ {:<47} │", truncated);
            }
            if block.ops.len() > ops_to_show {
                let _ = writeln!(
                    output,
                    "│ ... ({} more ops)                               │",
                    block.ops.len() - ops_to_show
                );
            }

            let term_str = match &block.terminator {
                r2ssa::cfg::BlockTerminator::Fallthrough { next } => format!("→ 0x{:x}", next),
                r2ssa::cfg::BlockTerminator::Branch { target } => format!("jmp 0x{:x}", target),
                r2ssa::cfg::BlockTerminator::ConditionalBranch {
                    true_target,
                    false_target,
                } => format!("jcc t:0x{:x} f:0x{:x}", true_target, false_target),
                r2ssa::cfg::BlockTerminator::Return => "ret".to_string(),
                r2ssa::cfg::BlockTerminator::Call { target, .. } => format!("call 0x{:x}", target),
                r2ssa::cfg::BlockTerminator::IndirectBranch => "jmp [reg]".to_string(),
                r2ssa::cfg::BlockTerminator::IndirectCall { .. } => "call [reg]".to_string(),
                r2ssa::cfg::BlockTerminator::Switch { cases, .. } => {
                    format!("switch ({} cases)", cases.len())
                }
                r2ssa::cfg::BlockTerminator::None => "???".to_string(),
            };
            let _ = writeln!(output, "│ {:<47} │", term_str);
            let _ = writeln!(
                output,
                "└─────────────────────────────────────────────────┘"
            );

            match &block.terminator {
                r2ssa::cfg::BlockTerminator::ConditionalBranch {
                    true_target,
                    false_target,
                } => {
                    let _ = writeln!(output, "        │ t         f │");
                    let _ = writeln!(output, "        ├─────┐ ┌─────┤");
                    let _ = writeln!(output, "        v     │ │     v");
                    let _ = writeln!(output, "   [0x{:x}]    [0x{:x}]", true_target, false_target);
                }
                r2ssa::cfg::BlockTerminator::Branch { target } => {
                    let _ = writeln!(output, "        │");
                    let _ = writeln!(output, "        v");
                    let _ = writeln!(output, "   [0x{:x}]", target);
                }
                r2ssa::cfg::BlockTerminator::Fallthrough { next } => {
                    let _ = writeln!(output, "        │");
                    let _ = writeln!(output, "        v");
                    let _ = writeln!(output, "   [0x{:x}]", next);
                }
                _ => {}
            }
            let _ = writeln!(output);
        }
    }

    output
}

fn format_r2il_op_short(op: &R2ILOp, disasm: &r2sleigh_lift::Disassembler) -> String {
    match op {
        R2ILOp::Copy { dst, src } => {
            format!(
                "{} = {}",
                disasm.format_varnode(dst),
                disasm.format_varnode(src)
            )
        }
        R2ILOp::Load { dst, addr, .. } => {
            format!(
                "{} = [{}]",
                disasm.format_varnode(dst),
                disasm.format_varnode(addr)
            )
        }
        R2ILOp::Store { addr, val, .. } => {
            format!(
                "[{}] = {}",
                disasm.format_varnode(addr),
                disasm.format_varnode(val)
            )
        }
        R2ILOp::IntAdd { dst, a, b } => format!(
            "{} = {} + {}",
            disasm.format_varnode(dst),
            disasm.format_varnode(a),
            disasm.format_varnode(b)
        ),
        R2ILOp::IntSub { dst, a, b } => format!(
            "{} = {} - {}",
            disasm.format_varnode(dst),
            disasm.format_varnode(a),
            disasm.format_varnode(b)
        ),
        R2ILOp::IntAnd { dst, a, b } => format!(
            "{} = {} & {}",
            disasm.format_varnode(dst),
            disasm.format_varnode(a),
            disasm.format_varnode(b)
        ),
        R2ILOp::IntOr { dst, a, b } => format!(
            "{} = {} | {}",
            disasm.format_varnode(dst),
            disasm.format_varnode(a),
            disasm.format_varnode(b)
        ),
        R2ILOp::IntXor { dst, a, b } => format!(
            "{} = {} ^ {}",
            disasm.format_varnode(dst),
            disasm.format_varnode(a),
            disasm.format_varnode(b)
        ),
        R2ILOp::IntEqual { dst, a, b } => format!(
            "{} = {} == {}",
            disasm.format_varnode(dst),
            disasm.format_varnode(a),
            disasm.format_varnode(b)
        ),
        R2ILOp::IntLess { dst, a, b } => format!(
            "{} = {} < {}",
            disasm.format_varnode(dst),
            disasm.format_varnode(a),
            disasm.format_varnode(b)
        ),
        R2ILOp::Branch { target } => format!("jmp {}", disasm.format_varnode(target)),
        R2ILOp::CBranch { cond, target } => {
            format!(
                "if {} jmp {}",
                disasm.format_varnode(cond),
                disasm.format_varnode(target)
            )
        }
        R2ILOp::Call { target } => format!("call {}", disasm.format_varnode(target)),
        R2ILOp::Return { .. } => "ret".to_string(),
        R2ILOp::Nop => "nop".to_string(),
        _ => format!("{:?}", op).chars().take(40).collect(),
    }
}

#[derive(Serialize)]
struct CFGJson {
    entry: u64,
    num_blocks: usize,
    blocks: Vec<CFGBlockJson>,
    edges: Vec<CFGEdgeJson>,
}

#[derive(Serialize)]
struct CFGBlockJson {
    addr: u64,
    size: u32,
    num_ops: usize,
    terminator: String,
    successors: Vec<u64>,
}

#[derive(Serialize)]
struct CFGEdgeJson {
    from: u64,
    to: u64,
    edge_type: String,
}

/// Get CFG as JSON.
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2cfg_function_json(
    _ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
) -> *mut std::os::raw::c_char {
    let Some(blocks) = (unsafe { BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return ptr::null_mut();
    };

    let cfg = match r2ssa::CFG::from_blocks(blocks.as_slice()) {
        Some(cfg) => cfg,
        None => return ptr::null_mut(),
    };

    let mut json_blocks = Vec::new();
    let mut json_edges = Vec::new();
    for addr in cfg.block_addrs() {
        if let Some(block) = cfg.get_block(addr) {
            let term_str = match &block.terminator {
                r2ssa::cfg::BlockTerminator::Fallthrough { .. } => "fallthrough",
                r2ssa::cfg::BlockTerminator::Branch { .. } => "branch",
                r2ssa::cfg::BlockTerminator::ConditionalBranch { .. } => "conditional",
                r2ssa::cfg::BlockTerminator::Return => "return",
                r2ssa::cfg::BlockTerminator::Call { .. } => "call",
                r2ssa::cfg::BlockTerminator::IndirectBranch => "indirect_branch",
                r2ssa::cfg::BlockTerminator::IndirectCall { .. } => "indirect_call",
                r2ssa::cfg::BlockTerminator::Switch { .. } => "switch",
                r2ssa::cfg::BlockTerminator::None => "none",
            };

            json_blocks.push(CFGBlockJson {
                addr,
                size: block.size,
                num_ops: block.ops.len(),
                terminator: term_str.to_string(),
                successors: cfg.successors(addr),
            });

            for succ in cfg.successors(addr) {
                let edge_type = cfg
                    .edge_type(addr, succ)
                    .map(|e| format!("{:?}", e))
                    .unwrap_or_else(|| "unknown".to_string());
                json_edges.push(CFGEdgeJson {
                    from: addr,
                    to: succ,
                    edge_type,
                });
            }
        }
    }

    let cfg_json = CFGJson {
        entry: cfg.entry,
        num_blocks: cfg.num_blocks(),
        blocks: json_blocks,
        edges: json_edges,
    };

    match serde_json::to_string_pretty(&cfg_json) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}
