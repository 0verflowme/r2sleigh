//! ESIL formatting helpers shared by the CLI and plugin.

use crate::disasm::Disassembler;
use r2il::R2ILOp;

/// Format an R2ILOp with resolved register names.
///
/// This function provides human-readable formatting of r2il operations
/// with register names resolved from the Sleigh specification.
pub fn format_op(disasm: &Disassembler, op: &R2ILOp) -> String {
    use r2il::R2ILOp::*;

    // Helper closure for formatting varnodes
    let vn = |v: &r2il::Varnode| disasm.format_varnode(v);

    match op {
        // Data movement
        Copy { dst, src } => format!("Copy {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        Load { dst, space, addr } => {
            format!(
                "Load {{ dst: {}, space: {:?}, addr: {} }}",
                vn(dst),
                space,
                vn(addr)
            )
        }
        Store { space, addr, val } => {
            format!(
                "Store {{ space: {:?}, addr: {}, val: {} }}",
                space,
                vn(addr),
                vn(val)
            )
        }
        Fence { ordering } => format!("Fence {{ ordering: {:?} }}", ordering),
        LoadLinked {
            dst,
            space,
            addr,
            ordering,
        } => {
            format!(
                "LoadLinked {{ dst: {}, space: {:?}, addr: {}, ordering: {:?} }}",
                vn(dst),
                space,
                vn(addr),
                ordering
            )
        }
        StoreConditional {
            result,
            space,
            addr,
            val,
            ordering,
        } => {
            let result_str = result
                .as_ref()
                .map(&vn)
                .unwrap_or_else(|| "none".to_string());
            format!(
                "StoreConditional {{ result: {}, space: {:?}, addr: {}, val: {}, ordering: {:?} }}",
                result_str,
                space,
                vn(addr),
                vn(val),
                ordering
            )
        }
        AtomicCAS {
            dst,
            space,
            addr,
            expected,
            replacement,
            ordering,
        } => {
            format!(
                "AtomicCAS {{ dst: {}, space: {:?}, addr: {}, expected: {}, replacement: {}, ordering: {:?} }}",
                vn(dst),
                space,
                vn(addr),
                vn(expected),
                vn(replacement),
                ordering
            )
        }
        LoadGuarded {
            dst,
            space,
            addr,
            guard,
            ordering,
        } => {
            format!(
                "LoadGuarded {{ dst: {}, space: {:?}, addr: {}, guard: {}, ordering: {:?} }}",
                vn(dst),
                space,
                vn(addr),
                vn(guard),
                ordering
            )
        }
        StoreGuarded {
            space,
            addr,
            val,
            guard,
            ordering,
        } => {
            format!(
                "StoreGuarded {{ space: {:?}, addr: {}, val: {}, guard: {}, ordering: {:?} }}",
                space,
                vn(addr),
                vn(val),
                vn(guard),
                ordering
            )
        }

        // Integer arithmetic
        IntAdd { dst, a, b } => {
            format!("IntAdd {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        IntSub { dst, a, b } => {
            format!("IntSub {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        IntMult { dst, a, b } => {
            format!("IntMult {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        IntDiv { dst, a, b } => {
            format!("IntDiv {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        IntSDiv { dst, a, b } => {
            format!("IntSDiv {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        IntRem { dst, a, b } => {
            format!("IntRem {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        IntSRem { dst, a, b } => {
            format!("IntSRem {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        IntNegate { dst, src } => format!("IntNegate {{ dst: {}, src: {} }}", vn(dst), vn(src)),

        // Bitwise operations
        IntAnd { dst, a, b } => {
            format!("IntAnd {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        IntOr { dst, a, b } => format!("IntOr {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b)),
        IntXor { dst, a, b } => {
            format!("IntXor {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        IntNot { dst, src } => format!("IntNot {{ dst: {}, src: {} }}", vn(dst), vn(src)),

        // Shift operations
        IntLeft { dst, a, b } => {
            format!("IntLeft {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        IntRight { dst, a, b } => format!(
            "IntRight {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        IntSRight { dst, a, b } => format!(
            "IntSRight {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),

        // Comparison operations
        IntEqual { dst, a, b } => format!(
            "IntEqual {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        IntNotEqual { dst, a, b } => format!(
            "IntNotEqual {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        IntLess { dst, a, b } => {
            format!("IntLess {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        IntSLess { dst, a, b } => format!(
            "IntSLess {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        IntLessEqual { dst, a, b } => format!(
            "IntLessEqual {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        IntSLessEqual { dst, a, b } => format!(
            "IntSLessEqual {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),

        // Carry/borrow
        IntCarry { dst, a, b } => format!(
            "IntCarry {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        IntSCarry { dst, a, b } => format!(
            "IntSCarry {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        IntSBorrow { dst, a, b } => format!(
            "IntSBorrow {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),

        // Extension
        IntZExt { dst, src } => format!("IntZExt {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        IntSExt { dst, src } => format!("IntSExt {{ dst: {}, src: {} }}", vn(dst), vn(src)),

        // Boolean operations
        BoolNot { dst, src } => format!("BoolNot {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        BoolAnd { dst, a, b } => {
            format!("BoolAnd {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        BoolOr { dst, a, b } => {
            format!("BoolOr {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }
        BoolXor { dst, a, b } => {
            format!("BoolXor {{ dst: {}, a: {}, b: {} }}", vn(dst), vn(a), vn(b))
        }

        // Bit manipulation
        Piece { dst, hi, lo } => format!(
            "Piece {{ dst: {}, hi: {}, lo: {} }}",
            vn(dst),
            vn(hi),
            vn(lo)
        ),
        Subpiece { dst, src, offset } => format!(
            "Subpiece {{ dst: {}, src: {}, offset: {} }}",
            vn(dst),
            vn(src),
            offset
        ),
        PopCount { dst, src } => format!("PopCount {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        Lzcount { dst, src } => format!("Lzcount {{ dst: {}, src: {} }}", vn(dst), vn(src)),

        // Control flow
        Branch { target } => format!("Branch {{ target: {} }}", vn(target)),
        CBranch { target, cond } => {
            format!("CBranch {{ target: {}, cond: {} }}", vn(target), vn(cond))
        }
        BranchInd { target } => format!("BranchInd {{ target: {} }}", vn(target)),
        Call { target } => format!("Call {{ target: {} }}", vn(target)),
        CallInd { target } => format!("CallInd {{ target: {} }}", vn(target)),
        Return { target } => format!("Return {{ target: {} }}", vn(target)),
        CallOther {
            output,
            userop,
            inputs,
        } => {
            let out_str = output
                .as_ref()
                .map(&vn)
                .unwrap_or_else(|| "none".to_string());
            let in_str: Vec<String> = inputs.iter().map(&vn).collect();
            let userop_str = match disasm.userop_name(*userop) {
                Some(name) => format!("{} ({})", userop, name),
                None => userop.to_string(),
            };
            format!(
                "CallOther {{ output: {}, userop: {}, inputs: [{}] }}",
                out_str,
                userop_str,
                in_str.join(", ")
            )
        }

        // Floating point
        FloatAdd { dst, a, b } => format!(
            "FloatAdd {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        FloatSub { dst, a, b } => format!(
            "FloatSub {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        FloatMult { dst, a, b } => format!(
            "FloatMult {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        FloatDiv { dst, a, b } => format!(
            "FloatDiv {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        FloatNeg { dst, src } => format!("FloatNeg {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        FloatAbs { dst, src } => format!("FloatAbs {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        FloatSqrt { dst, src } => format!("FloatSqrt {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        FloatCeil { dst, src } => format!("FloatCeil {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        FloatFloor { dst, src } => format!("FloatFloor {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        FloatRound { dst, src } => format!("FloatRound {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        FloatNaN { dst, src } => format!("FloatNaN {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        FloatEqual { dst, a, b } => format!(
            "FloatEqual {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        FloatNotEqual { dst, a, b } => format!(
            "FloatNotEqual {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        FloatLess { dst, a, b } => format!(
            "FloatLess {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        FloatLessEqual { dst, a, b } => format!(
            "FloatLessEqual {{ dst: {}, a: {}, b: {} }}",
            vn(dst),
            vn(a),
            vn(b)
        ),
        Int2Float { dst, src } => format!("Int2Float {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        Float2Int { dst, src } => format!("Float2Int {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        FloatFloat { dst, src } => format!("FloatFloat {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        Trunc { dst, src } => format!("Trunc {{ dst: {}, src: {} }}", vn(dst), vn(src)),

        // Analysis operations
        Multiequal { dst, inputs } => {
            let in_str: Vec<String> = inputs.iter().map(&vn).collect();
            format!(
                "Multiequal {{ dst: {}, inputs: [{}] }}",
                vn(dst),
                in_str.join(", ")
            )
        }
        Indirect { dst, src, indirect } => {
            format!(
                "Indirect {{ dst: {}, src: {}, indirect: {} }}",
                vn(dst),
                vn(src),
                vn(indirect)
            )
        }
        Cast { dst, src } => format!("Cast {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        New { dst, src } => format!("New {{ dst: {}, src: {} }}", vn(dst), vn(src)),
        CpuId { dst } => format!("CpuId {{ dst: {} }}", vn(dst)),

        // Pointer operations
        PtrAdd {
            dst,
            base,
            index,
            element_size,
        } => {
            format!(
                "PtrAdd {{ dst: {}, base: {}, index: {}, element_size: {} }}",
                vn(dst),
                vn(base),
                vn(index),
                element_size
            )
        }
        PtrSub {
            dst,
            base,
            index,
            element_size,
        } => {
            format!(
                "PtrSub {{ dst: {}, base: {}, index: {}, element_size: {} }}",
                vn(dst),
                vn(base),
                vn(index),
                element_size
            )
        }
        SegmentOp {
            dst,
            segment,
            offset,
        } => {
            format!(
                "SegmentOp {{ dst: {}, segment: {}, offset: {} }}",
                vn(dst),
                vn(segment),
                vn(offset)
            )
        }

        // Bit manipulation
        Insert {
            dst,
            src,
            value,
            position,
        } => {
            format!(
                "Insert {{ dst: {}, src: {}, value: {}, position: {} }}",
                vn(dst),
                vn(src),
                vn(value),
                vn(position)
            )
        }
        Extract { dst, src, position } => {
            format!(
                "Extract {{ dst: {}, src: {}, position: {} }}",
                vn(dst),
                vn(src),
                vn(position)
            )
        }
        Select {
            dst,
            cond,
            if_true,
            if_false,
        } => format!(
            "Select {{ dst: {}, cond: {}, if_true: {}, if_false: {} }}",
            vn(dst),
            vn(cond),
            vn(if_true),
            vn(if_false)
        ),

        // Special
        Nop => "Nop".to_string(),
        Unimplemented => "Unimplemented".to_string(),
        Breakpoint => "Breakpoint".to_string(),
    }
}

/// Convert an R2ILOp into an ESIL string.
///
/// ESIL (Evaluable Strings Intermediate Language) uses reverse Polish notation:
/// - `a,b,+` = a + b
/// - `a,b,=` = b = a (assignment)
/// - `a,[N]` = read N bytes from address a
/// - `a,b,=[N]` = write N bytes of b to address a
pub fn op_to_esil(disasm: &Disassembler, op: &R2ILOp) -> String {
    use r2il::R2ILOp::*;

    // Helper to format varnode as lowercase ESIL operand
    let vn = |v: &r2il::Varnode| disasm.format_varnode(v).to_lowercase();

    // Helper to get size suffix for memory operations
    let size_suffix = |size: u32| -> String {
        match size {
            1 => "[1]".to_string(),
            2 => "[2]".to_string(),
            4 => "[4]".to_string(),
            8 => "[8]".to_string(),
            _ => format!("[{}]", size),
        }
    };

    match op {
        // ========== Data Movement ==========
        Copy { dst, src } => format!("{},{},=", vn(src), vn(dst)),

        Load { dst, addr, .. } => {
            let sz = size_suffix(dst.size);
            format!("{},{},{},=", vn(addr), sz, vn(dst))
        }

        Store { addr, val, .. } => {
            let sz = size_suffix(val.size);
            format!("{},{},={}", vn(val), vn(addr), sz)
        }
        Fence { .. } => String::new(),
        LoadLinked { dst, addr, .. } => {
            let sz = size_suffix(dst.size);
            format!("{},{},{},=", vn(addr), sz, vn(dst))
        }
        StoreConditional {
            result, addr, val, ..
        } => {
            let sz = size_suffix(val.size);
            // Baseline LL/SC modeling: we only encode the success path in ESIL.
            // SC success is architecturally reported as 0 (non-zero means failure).
            match result {
                Some(dst) => format!("{},{},={},0,{},=", vn(val), vn(addr), sz, vn(dst)),
                None => format!("{},{},={}", vn(val), vn(addr), sz),
            }
        }
        AtomicCAS {
            dst,
            addr,
            expected,
            replacement,
            ..
        } => {
            let sz = size_suffix(dst.size);
            format!(
                "{},{},{},={},{},==,?{{,{},{}={},}}",
                vn(addr),
                sz,
                vn(dst),
                vn(dst),
                vn(expected),
                vn(replacement),
                vn(addr),
                sz
            )
        }
        LoadGuarded {
            dst, addr, guard, ..
        } => {
            let sz = size_suffix(dst.size);
            format!("{},?{{,{},{},{},=,}}", vn(guard), vn(addr), sz, vn(dst))
        }
        StoreGuarded {
            addr, val, guard, ..
        } => {
            let sz = size_suffix(val.size);
            format!("{},?{{,{},{},={},}}", vn(guard), vn(val), vn(addr), sz)
        }

        // ========== Integer Arithmetic ==========
        IntAdd { dst, a, b } => format!("{},{},+,{},=", vn(a), vn(b), vn(dst)),
        IntSub { dst, a, b } => format!("{},{},-,{},=", vn(a), vn(b), vn(dst)),
        IntMult { dst, a, b } => format!("{},{},*,{},=", vn(a), vn(b), vn(dst)),
        IntDiv { dst, a, b } => format!("{},{},/,{},=", vn(a), vn(b), vn(dst)),
        IntSDiv { dst, a, b } => format!("{},{},~/,{},=", vn(a), vn(b), vn(dst)),
        IntRem { dst, a, b } => format!("{},{},%,{},=", vn(a), vn(b), vn(dst)),
        IntSRem { dst, a, b } => format!("{},{},~%,{},=", vn(a), vn(b), vn(dst)),
        IntNegate { dst, src } => format!("{},0,-,{},=", vn(src), vn(dst)),

        // Carry/borrow operations (set flags)
        IntCarry { dst, a, b } => format!("{},{},+,$c,{},=", vn(a), vn(b), vn(dst)),
        IntSCarry { dst, a, b } => format!("{},{},+,$o,{},=", vn(a), vn(b), vn(dst)),
        IntSBorrow { dst, a, b } => format!("{},{},-,$b,{},=", vn(a), vn(b), vn(dst)),

        // ========== Logical Operations ==========
        IntAnd { dst, a, b } => format!("{},{},&,{},=", vn(a), vn(b), vn(dst)),
        IntOr { dst, a, b } => format!("{},{},|,{},=", vn(a), vn(b), vn(dst)),
        IntXor { dst, a, b } => format!("{},{},^,{},=", vn(a), vn(b), vn(dst)),
        IntNot { dst, src } => format!("{},~,{},=", vn(src), vn(dst)),

        // ========== Shift Operations ==========
        IntLeft { dst, a, b } => format!("{},{},<<,{},=", vn(a), vn(b), vn(dst)),
        IntRight { dst, a, b } => format!("{},{},>>,{},=", vn(a), vn(b), vn(dst)),
        IntSRight { dst, a, b } => format!("{},{},>>>,{},=", vn(a), vn(b), vn(dst)),

        // ========== Comparison Operations ==========
        IntEqual { dst, a, b } => format!("{},{},==,{},=", vn(a), vn(b), vn(dst)),
        IntNotEqual { dst, a, b } => format!("{},{},==,!,{},=", vn(a), vn(b), vn(dst)),
        IntLess { dst, a, b } => format!("{},{},<,{},=", vn(a), vn(b), vn(dst)),
        IntSLess { dst, a, b } => format!("{},{},<$,{},=", vn(a), vn(b), vn(dst)),
        IntLessEqual { dst, a, b } => format!("{},{},<=,{},=", vn(a), vn(b), vn(dst)),
        IntSLessEqual { dst, a, b } => format!("{},{},<=$,{},=", vn(a), vn(b), vn(dst)),

        // ========== Extension Operations ==========
        // Zero/sign extension - in ESIL, size is implicit in destination
        IntZExt { dst, src } => format!("{},{},=", vn(src), vn(dst)),
        IntSExt { dst, src } => {
            // Sign extension: use ~~ operator (value,bits,~~)
            let src_bits = src.size * 8;
            format!("{},{},~~,{},=", vn(src), src_bits, vn(dst))
        }

        // ========== Boolean Operations ==========
        BoolNot { dst, src } => format!("{},!,{},=", vn(src), vn(dst)),
        BoolAnd { dst, a, b } => format!("{},{},&&,{},=", vn(a), vn(b), vn(dst)),
        BoolOr { dst, a, b } => format!("{},{},||,{},=", vn(a), vn(b), vn(dst)),
        BoolXor { dst, a, b } => format!("{},{},^^,{},=", vn(a), vn(b), vn(dst)),

        // ========== Bit Manipulation ==========
        Piece { dst, hi, lo } => {
            // Concatenate: dst = (hi << lo.size*8) | lo
            let shift = lo.size * 8;
            format!("{},{},<<,{},|,{},=", vn(hi), shift, vn(lo), vn(dst))
        }

        Subpiece { dst, src, offset } => {
            // Extract: dst = (src >> offset*8) & mask
            let shift = offset * 8;
            if shift > 0 {
                format!("{},{},>>,{},=", vn(src), shift, vn(dst))
            } else {
                format!("{},{},=", vn(src), vn(dst))
            }
        }

        PopCount { dst, src } => format!("{},POPCOUNT,{},=", vn(src), vn(dst)),
        Lzcount { dst, src } => format!("{},CLZ,{},=", vn(src), vn(dst)),

        // ========== Control Flow ==========
        Branch { target } => format!("{},pc,=", vn(target)),

        CBranch { target, cond } => {
            // Conditional branch: if cond then goto target
            format!("{},?{{,{},pc,=,}}", vn(cond), vn(target))
        }

        BranchInd { target } => format!("{},pc,=", vn(target)),

        Call { target } => {
            let ptr_size = ptr_size_for_arch(disasm);
            let sp = stack_reg_for_arch(disasm);
            format_call_esil(&vn(target), sp, ptr_size)
        }

        CallInd { target } => {
            let ptr_size = ptr_size_for_arch(disasm);
            let sp = stack_reg_for_arch(disasm);
            format_call_esil(&vn(target), sp, ptr_size)
        }

        Return { target: _ } => {
            let ptr_size = ptr_size_for_arch(disasm);
            let sp = stack_reg_for_arch(disasm);
            format_return_esil(sp, ptr_size)
        }

        // ========== Floating Point ==========
        FloatAdd { dst, a, b } => format!("{},{},F+,{},=", vn(a), vn(b), vn(dst)),
        FloatSub { dst, a, b } => format!("{},{},F-,{},=", vn(a), vn(b), vn(dst)),
        FloatMult { dst, a, b } => format!("{},{},F*,{},=", vn(a), vn(b), vn(dst)),
        FloatDiv { dst, a, b } => format!("{},{},F/,{},=", vn(a), vn(b), vn(dst)),
        FloatNeg { dst, src } => format!("0,{},F-,{},=", vn(src), vn(dst)),
        FloatAbs { dst, src } => format!("{},FABS,{},=", vn(src), vn(dst)),
        FloatSqrt { dst, src } => format!("{},FSQRT,{},=", vn(src), vn(dst)),
        FloatCeil { dst, src } => format!("{},FCEIL,{},=", vn(src), vn(dst)),
        FloatFloor { dst, src } => format!("{},FFLOOR,{},=", vn(src), vn(dst)),
        FloatRound { dst, src } => format!("{},FROUND,{},=", vn(src), vn(dst)),
        FloatNaN { dst, src } => format!("{},FISNAN,{},=", vn(src), vn(dst)),
        FloatEqual { dst, a, b } => format!("{},{},F==,{},=", vn(a), vn(b), vn(dst)),
        FloatNotEqual { dst, a, b } => format!("{},{},F==,!,{},=", vn(a), vn(b), vn(dst)),
        FloatLess { dst, a, b } => format!("{},{},F<,{},=", vn(a), vn(b), vn(dst)),
        FloatLessEqual { dst, a, b } => format!("{},{},F<=,{},=", vn(a), vn(b), vn(dst)),
        Int2Float { dst, src } => format!("{},I2F,{},=", vn(src), vn(dst)),
        Float2Int { dst, src } => format!("{},F2I,{},=", vn(src), vn(dst)),
        FloatFloat { dst, src } => format!("{},F2F,{},=", vn(src), vn(dst)),
        Trunc { dst, src } => format!("{},FTRUNC,{},=", vn(src), vn(dst)),

        // ========== Special Operations ==========
        CallOther {
            output,
            userop,
            inputs,
        } => format_callother_esil(disasm, output, *userop, inputs, false),

        Nop => String::new(),
        Unimplemented => "UNIMPL".to_string(),
        CpuId { dst } => format!("CPUID,{},=", vn(dst)),
        Breakpoint => "BREAK".to_string(),

        // Analysis operations (typically not in raw P-code from disassembly)
        Multiequal { dst, inputs } => {
            let args: Vec<String> = inputs.iter().map(&vn).collect();
            format!("{},PHI,{},=", args.join(","), vn(dst))
        }

        Indirect { dst, src, .. } => format!("{},{},=", vn(src), vn(dst)),

        PtrAdd {
            dst,
            base,
            index,
            element_size,
        } => {
            format!(
                "{},{},{},*,+,{},=",
                vn(base),
                vn(index),
                element_size,
                vn(dst)
            )
        }

        PtrSub {
            dst,
            base,
            index,
            element_size,
        } => {
            format!(
                "{},{},{},*,-,{},=",
                vn(base),
                vn(index),
                element_size,
                vn(dst)
            )
        }

        SegmentOp {
            dst,
            segment,
            offset,
        } => {
            // Segment:offset calculation (x86 real mode style)
            format!("{},4,<<,{},+,{},=", vn(segment), vn(offset), vn(dst))
        }

        New { dst, src } => format!("{},NEW,{},=", vn(src), vn(dst)),
        Cast { dst, src } => format!("{},{},=", vn(src), vn(dst)),

        Extract { dst, src, position } => {
            format!("{},{},>>,{},=", vn(src), vn(position), vn(dst))
        }

        Insert {
            dst,
            src,
            value,
            position,
        } => {
            // Insert value into src at position
            format!(
                "{},{},<<,{},|,{},=",
                vn(value),
                vn(position),
                vn(src),
                vn(dst)
            )
        }
        Select {
            dst,
            cond,
            if_true,
            if_false,
        } => format!(
            "{},?{{,{},{},=,}}{{,{},{},=,}}",
            vn(cond),
            vn(if_true),
            vn(dst),
            vn(if_false),
            vn(dst)
        ),
    }
}

fn stack_reg_for_arch(disasm: &Disassembler) -> &'static str {
    let arch = disasm.arch_name().to_ascii_lowercase();
    if arch.contains("x86") {
        if arch.contains("64") { "rsp" } else { "esp" }
    } else {
        "sp"
    }
}

fn ptr_size_for_arch(disasm: &Disassembler) -> u32 {
    let arch = disasm.arch_name().to_ascii_lowercase();
    if arch.contains("64") {
        8
    } else if arch.contains("16") {
        2
    } else {
        4
    }
}

fn format_call_esil(target: &str, sp_reg: &str, ptr_size: u32) -> String {
    format!("pc,{ptr_size},{sp_reg},-=,{sp_reg},=[{ptr_size}],{target},pc,=")
}

fn format_return_esil(sp_reg: &str, ptr_size: u32) -> String {
    format!("{sp_reg},[{ptr_size}],pc,=,{ptr_size},{sp_reg},+=")
}

/// Convert an R2ILOp into an ESIL string with userop names (best-effort).
pub fn op_to_esil_named(disasm: &Disassembler, op: &R2ILOp) -> String {
    match op {
        R2ILOp::CallOther {
            output,
            userop,
            inputs,
        } => format_callother_esil(disasm, output, *userop, inputs, true),
        _ => op_to_esil(disasm, op),
    }
}

fn callother_userop_label(disasm: &Disassembler, userop: u32, include_name: bool) -> String {
    if include_name && let Some(name) = disasm.userop_name(userop) {
        return format!("{}:{}", userop, name);
    }
    userop.to_string()
}

fn format_callother_esil(
    disasm: &Disassembler,
    output: &Option<r2il::Varnode>,
    userop: u32,
    inputs: &[r2il::Varnode],
    include_name: bool,
) -> String {
    let vn = |v: &r2il::Varnode| disasm.format_varnode(v).to_lowercase();
    let args: Vec<String> = inputs.iter().map(&vn).collect();
    let args_str = args.join(",");
    let userop_str = callother_userop_label(disasm, userop, include_name);
    match output {
        Some(dst) => format!("{},CALLOTHER({}),{},=", args_str, userop_str, vn(dst)),
        None => format!("{},CALLOTHER({})", args_str, userop_str),
    }
}

#[cfg(test)]
mod tests {
    use super::{format_call_esil, format_return_esil};

    #[test]
    fn call_esil_uses_x86_64_stack_and_width() {
        let esil = format_call_esil("0x401000", "rsp", 8);
        assert_eq!(esil, "pc,8,rsp,-=,rsp,=[8],0x401000,pc,=");
    }

    #[test]
    fn call_esil_uses_arm64_stack_and_width() {
        let esil = format_call_esil("0x1000", "sp", 8);
        assert_eq!(esil, "pc,8,sp,-=,sp,=[8],0x1000,pc,=");
    }

    #[test]
    fn return_esil_supports_32bit_pointer_width() {
        let esil = format_return_esil("esp", 4);
        assert_eq!(esil, "esp,[4],pc,=,4,esp,+=");
    }
}
