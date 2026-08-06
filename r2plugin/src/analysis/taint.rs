use crate::blocks::BlockSlice;
use crate::{R2ILBlock, R2ILContext, SSAOpInfo, ssa_op_to_info};
use r2ssa::TaintPolicy;
use serde::{Deserialize, Serialize};
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::ptr;
use std::sync::{Mutex, OnceLock};

const R2TAINT_OP_OTHER: u32 = 0;
const R2TAINT_OP_CALL: u32 = 1;
const R2TAINT_OP_CALL_IND: u32 = 2;
const R2TAINT_OP_STORE: u32 = 3;

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(default)]
struct TaintConfig {
    sources: Vec<String>,
    sink_calls: bool,
    sink_stores: bool,
}

impl Default for TaintConfig {
    fn default() -> Self {
        Self {
            sources: Vec::new(),
            sink_calls: true,
            sink_stores: true,
        }
    }
}

fn taint_config() -> &'static Mutex<TaintConfig> {
    static CONFIG: OnceLock<Mutex<TaintConfig>> = OnceLock::new();
    CONFIG.get_or_init(|| Mutex::new(TaintConfig::default()))
}

#[derive(Serialize)]
struct TaintSourceJson {
    var: String,
    labels: Vec<String>,
    block: u64,
    block_hex: String,
}

#[derive(Serialize)]
struct TaintSinkJson {
    block: u64,
    block_hex: String,
    op_idx: usize,
    op: SSAOpInfo,
}

#[derive(Serialize)]
struct TaintedVarJson {
    var: String,
    labels: Vec<String>,
}

#[derive(Serialize)]
struct SinkHitJson {
    block: u64,
    block_hex: String,
    op_idx: usize,
    op: SSAOpInfo,
    tainted_vars: Vec<TaintedVarJson>,
}

#[derive(Serialize)]
struct TaintReportJson {
    sources: Vec<TaintSourceJson>,
    sinks: Vec<TaintSinkJson>,
    sink_hits: Vec<SinkHitJson>,
    tainted_vars: Vec<TaintedVarJson>,
}

#[derive(Serialize)]
struct TaintSummaryReportJson {
    sources: Vec<TaintSourceJson>,
    sink_hits: Vec<SinkHitJson>,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2TaintSource {
    block: u64,
    labels: *const *const c_char,
    num_labels: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2TaintTaintedVar {
    var: *const c_char,
    labels: *const *const c_char,
    num_labels: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2TaintSinkHit {
    block: u64,
    op_idx: usize,
    op_kind: u32,
    target_addr: u64,
    has_target_addr: i32,
    tainted_vars: *const R2TaintTaintedVar,
    num_tainted_vars: usize,
}

pub struct R2TaintFunctionSummary {
    sources: Vec<R2TaintSource>,
    sink_hits: Vec<R2TaintSinkHit>,
    _tainted_var_arrays: Vec<Vec<R2TaintTaintedVar>>,
    _label_arrays: Vec<Vec<*const c_char>>,
    _strings: Vec<CString>,
}

fn labels_to_strings(labels: &r2ssa::taint::TaintSet) -> Vec<String> {
    let mut out: Vec<String> = labels.iter().map(|l| l.id.clone()).collect();
    out.sort();
    out
}

fn current_taint_policy() -> Option<r2ssa::DefaultTaintPolicy> {
    let cfg = taint_config().lock().ok()?.clone();
    let mut policy = if cfg.sources.is_empty() {
        r2ssa::DefaultTaintPolicy::all_inputs()
    } else {
        r2ssa::DefaultTaintPolicy::new()
    }
    .with_sink_calls(cfg.sink_calls)
    .with_sink_stores(cfg.sink_stores);
    for src in cfg.sources {
        policy = policy.with_source(src);
    }
    Some(policy)
}

fn collect_taint_sources(
    ssa_func: &r2ssa::SSAFunction,
    policy: &r2ssa::DefaultTaintPolicy,
) -> Vec<TaintSourceJson> {
    let mut source_map = std::collections::HashMap::new();
    for block in ssa_func.blocks() {
        block.for_each_source(|src| {
            if let Some(labels) = policy.is_source(src.var, block.addr) {
                let entry = source_map
                    .entry(src.var.display_name())
                    .or_insert(TaintSourceJson {
                        var: src.var.display_name(),
                        labels: Vec::new(),
                        block: block.addr,
                        block_hex: format!("0x{:x}", block.addr),
                    });
                for label in labels {
                    entry.labels.push(label.id);
                }
            }
        });
    }

    for source in source_map.values_mut() {
        source.labels.sort();
        source.labels.dedup();
    }

    let mut sources: Vec<TaintSourceJson> = source_map.into_values().collect();
    sources.sort_by(|a, b| a.var.cmp(&b.var));
    sources
}

fn collect_taint_sink_hits(result: &r2ssa::TaintResult) -> Vec<SinkHitJson> {
    result
        .sink_hits
        .iter()
        .map(|hit| SinkHitJson {
            block: hit.block_addr,
            block_hex: format!("0x{:x}", hit.block_addr),
            op_idx: hit.op_idx,
            op: ssa_op_to_info(&hit.op),
            tainted_vars: hit
                .tainted_vars
                .iter()
                .map(|(var, labels)| TaintedVarJson {
                    var: var.display_name(),
                    labels: labels_to_strings(labels),
                })
                .collect(),
        })
        .collect()
}

fn build_taint_summary_report(
    ctx_ref: &R2ILContext,
    blocks: &[r2il::R2ILBlock],
) -> Option<TaintSummaryReportJson> {
    let ssa_func = r2ssa::SSAFunction::from_blocks_with_arch(blocks, ctx_ref.arch.as_ref())?;
    let policy = current_taint_policy()?;
    let sources = collect_taint_sources(&ssa_func, &policy);
    let analysis = r2ssa::TaintAnalysis::with_arch(&ssa_func, policy, ctx_ref.arch.as_ref());
    let result = analysis.analyze();

    Some(TaintSummaryReportJson {
        sources,
        sink_hits: collect_taint_sink_hits(&result),
    })
}

fn parse_taint_target_addr(name: &str) -> Option<u64> {
    let payload = name
        .strip_prefix("const:")
        .or_else(|| name.strip_prefix("ram:"))?;
    let payload = payload.split('_').next().unwrap_or_default();
    let payload = payload.strip_prefix("0x").unwrap_or(payload);
    if payload.is_empty() {
        return None;
    }
    u64::from_str_radix(payload, 16).ok()
}

fn ffi_push_string(strings: &mut Vec<CString>, value: &str) -> *const c_char {
    match CString::new(value) {
        Ok(s) => {
            strings.push(s);
            strings.last().map_or(ptr::null(), |s| s.as_ptr())
        }
        Err(_) => ptr::null(),
    }
}

fn ffi_label_array(
    labels: &[String],
    strings: &mut Vec<CString>,
    label_arrays: &mut Vec<Vec<*const c_char>>,
) -> (*const *const c_char, usize) {
    let mut ptrs = Vec::with_capacity(labels.len());
    for label in labels {
        let ptr = ffi_push_string(strings, label);
        if !ptr.is_null() {
            ptrs.push(ptr);
        }
    }
    let ptr = if ptrs.is_empty() {
        ptr::null()
    } else {
        ptrs.as_ptr()
    };
    let count = ptrs.len();
    label_arrays.push(ptrs);
    (ptr, count)
}

fn ffi_op_kind(op: &str) -> u32 {
    match op {
        "Call" => R2TAINT_OP_CALL,
        "CallInd" => R2TAINT_OP_CALL_IND,
        "Store" => R2TAINT_OP_STORE,
        _ => R2TAINT_OP_OTHER,
    }
}

fn ffi_taint_summary_from_report(report: TaintSummaryReportJson) -> R2TaintFunctionSummary {
    let mut strings = Vec::new();
    let mut label_arrays = Vec::new();
    let mut tainted_var_arrays = Vec::new();
    let mut sources = Vec::with_capacity(report.sources.len());
    let mut sink_hits = Vec::with_capacity(report.sink_hits.len());

    for source in report.sources {
        let (labels, num_labels) = ffi_label_array(&source.labels, &mut strings, &mut label_arrays);
        sources.push(R2TaintSource {
            block: source.block,
            labels,
            num_labels,
        });
    }

    for hit in report.sink_hits {
        let mut vars = Vec::with_capacity(hit.tainted_vars.len());
        for tainted_var in hit.tainted_vars {
            let var = ffi_push_string(&mut strings, &tainted_var.var);
            let (labels, num_labels) =
                ffi_label_array(&tainted_var.labels, &mut strings, &mut label_arrays);
            vars.push(R2TaintTaintedVar {
                var,
                labels,
                num_labels,
            });
        }
        let tainted_vars = if vars.is_empty() {
            ptr::null()
        } else {
            vars.as_ptr()
        };
        let num_tainted_vars = vars.len();
        tainted_var_arrays.push(vars);

        let target_addr = hit
            .op
            .sources
            .first()
            .and_then(|source| parse_taint_target_addr(source));
        sink_hits.push(R2TaintSinkHit {
            block: hit.block,
            op_idx: hit.op_idx,
            op_kind: ffi_op_kind(&hit.op.op),
            target_addr: target_addr.unwrap_or(0),
            has_target_addr: i32::from(target_addr.is_some()),
            tainted_vars,
            num_tainted_vars,
        });
    }

    R2TaintFunctionSummary {
        sources,
        sink_hits,
        _tainted_var_arrays: tainted_var_arrays,
        _label_arrays: label_arrays,
        _strings: strings,
    }
}

/// Configure taint sources/sinks via JSON.
/// If `json` is NULL or empty, returns the current configuration.
/// Caller must free the returned string with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2taint_sources_sinks_json(json: *const c_char) -> *mut c_char {
    if !json.is_null() {
        let json_str = unsafe {
            match CStr::from_ptr(json).to_str() {
                Ok(s) => s.trim(),
                Err(_) => return ptr::null_mut(),
            }
        };
        if !json_str.is_empty() {
            match serde_json::from_str::<TaintConfig>(json_str) {
                Ok(new_cfg) => {
                    if let Ok(mut cfg) = taint_config().lock() {
                        *cfg = new_cfg;
                    }
                }
                Err(_) => return ptr::null_mut(),
            }
        }
    }

    let cfg = match taint_config().lock() {
        Ok(cfg) => cfg.clone(),
        Err(_) => return ptr::null_mut(),
    };

    match serde_json::to_string_pretty(&cfg) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

/// Run taint analysis and return results as JSON.
/// Caller must free the returned string with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2taint_function_json(
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
    let policy = match current_taint_policy() {
        Some(policy) => policy,
        None => return ptr::null_mut(),
    };
    let sources = collect_taint_sources(&ssa_func, &policy);

    let mut sinks = Vec::new();
    for block in ssa_func.blocks() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            if policy.is_sink(op, block.addr) {
                sinks.push(TaintSinkJson {
                    block: block.addr,
                    block_hex: format!("0x{:x}", block.addr),
                    op_idx,
                    op: ssa_op_to_info(op),
                });
            }
        }
    }

    let analysis = r2ssa::TaintAnalysis::with_arch(&ssa_func, policy, ctx_ref.arch.as_ref());
    let result = analysis.analyze();

    let mut tainted_vars = Vec::new();
    for (name, labels) in result.var_taints.iter() {
        if labels.is_empty() {
            continue;
        }
        tainted_vars.push(TaintedVarJson {
            var: name.clone(),
            labels: labels_to_strings(labels),
        });
    }
    tainted_vars.sort_by(|a, b| a.var.cmp(&b.var));

    let report = TaintReportJson {
        sources,
        sinks,
        sink_hits: collect_taint_sink_hits(&result),
        tainted_vars,
    };

    match serde_json::to_string_pretty(&report) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

/// Run taint analysis and return post-analysis summary JSON.
/// Caller must free the returned string with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2taint_function_summary_json(
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

    let Some(report) = build_taint_summary_report(ctx_ref, blocks.as_slice()) else {
        return ptr::null_mut();
    };

    match serde_json::to_string(&report) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2taint_function_summary_typed(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
) -> *mut R2TaintFunctionSummary {
    if ctx.is_null() {
        return ptr::null_mut();
    }
    let Some(blocks) = (unsafe { BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return ptr::null_mut();
    };
    let ctx_ref = unsafe { &*ctx };
    let Some(report) = build_taint_summary_report(ctx_ref, blocks.as_slice()) else {
        return ptr::null_mut();
    };
    Box::into_raw(Box::new(ffi_taint_summary_from_report(report)))
}

#[unsafe(no_mangle)]
pub extern "C" fn r2taint_function_summary_sources(
    summary: *const R2TaintFunctionSummary,
    count: *mut usize,
) -> *const R2TaintSource {
    if summary.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let summary = unsafe { &*summary };
    if !count.is_null() {
        unsafe {
            *count = summary.sources.len();
        }
    }
    summary.sources.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2taint_function_summary_sink_hits(
    summary: *const R2TaintFunctionSummary,
    count: *mut usize,
) -> *const R2TaintSinkHit {
    if summary.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let summary = unsafe { &*summary };
    if !count.is_null() {
        unsafe {
            *count = summary.sink_hits.len();
        }
    }
    summary.sink_hits.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2taint_function_summary_free(summary: *mut R2TaintFunctionSummary) {
    if !summary.is_null() {
        unsafe {
            drop(Box::from_raw(summary));
        }
    }
}
