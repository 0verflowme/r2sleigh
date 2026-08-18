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
            format!(
                "CallOther {{ output: {}, userop: {}, inputs: [{}] }}",
                out_str,
                userop,
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

/// Number of value bits a varnode carries, clamped to what ESIL can express.
fn bit_width(v: &r2il::Varnode) -> u32 {
    (v.size.max(1) * 8).min(64)
}

/// All-ones mask for `bits`, as an ESIL literal.
fn mask_literal(bits: u32) -> String {
    if bits >= 64 {
        "0xffffffffffffffff".to_string()
    } else {
        format!("0x{:x}", (1u64 << bits) - 1)
    }
}

/// Sign bit of a `bits`-wide value, as an ESIL literal.
fn sign_bit_literal(bits: u32) -> String {
    format!("0x{:x}", 1u64 << (bits.min(64) - 1))
}

/// ESIL leaves the zero flag, borrow and overflow of the previous `==` on
/// `esil->old` / `esil->cur`, so every comparison below starts by pushing its
/// operands into one `==` and then reads the flags it needs. `<` and `>` are
/// deliberately unused: they compare signed against `esil->lastsz`, which is
/// the width of the last register touched and is meaningless for the unique
/// space temporaries most P-code operands live in.
fn compare_prologue(a: &str, b: &str) -> String {
    format!("{b},{a},==")
}

/// `$o` reports the overflow radare2's own lifters expect, except when the
/// subtrahend is the sign bit itself; the extra term restores that case.
fn signed_overflow_terms(b: &str, bits: u32) -> String {
    format!("{},$o,{},{},-,!,^", bits - 1, sign_bit_literal(bits), b)
}

/// Convert an R2ILOp into an ESIL string.
///
/// ESIL (Evaluable Strings Intermediate Language) uses reverse Polish notation
/// in which the *last* operand pushed is the left-hand side of the operation:
/// - `a,b,+` = b + a
/// - `a,b,-` = b - a
/// - `a,b,=` = b = a (assignment)
/// - `a,[N]` = read N bytes from address a
/// - `a,b,=[N]` = write N bytes of b to address a
pub fn op_to_esil(disasm: &Disassembler, op: &R2ILOp) -> String {
    use r2il::R2ILOp::*;

    // Helper to format varnode as a lowercase ESIL operand. A ram varnode names
    // a memory cell, so reading its value is a load, not a bare address.
    let vn = |v: &r2il::Varnode| -> String {
        match v.space {
            r2il::SpaceId::Ram => format!("0x{:x},[{}]", v.offset, v.size.clamp(1, 8)),
            _ => disasm.format_varnode(v).to_lowercase(),
        }
    };

    // The same varnode used as an address rather than as a value.
    let vaddr = |v: &r2il::Varnode| -> String {
        match v.space {
            r2il::SpaceId::Ram => format!("0x{:x}", v.offset),
            _ => disasm.format_varnode(v).to_lowercase(),
        }
    };

    // Assignment suffix for a destination varnode.
    let asg = |v: &r2il::Varnode| -> String {
        match v.space {
            r2il::SpaceId::Ram => format!("0x{:x},=[{}]", v.offset, v.size.clamp(1, 8)),
            _ => format!("{},=", disasm.format_varnode(v).to_lowercase()),
        }
    };

    // Helper to get size suffix for memory operations. ESIL only defines the
    // widths below, so anything else is clamped rather than spelled as an
    // operator radare2 would not recognise.
    let size_suffix = |size: u32| -> String {
        match size {
            1 | 2 | 3 | 4 | 8 | 16 => format!("[{size}]"),
            0 => "[1]".to_string(),
            n if n < 8 => format!("[{}]", n.next_power_of_two()),
            n if n < 16 => "[8]".to_string(),
            _ => "[16]".to_string(),
        }
    };

    match op {
        // ========== Data Movement ==========
        Copy { dst, src } => format!("{},{}", vn(src), asg(dst)),

        Load { dst, addr, .. } => {
            let sz = size_suffix(dst.size);
            format!("{},{},{}", vn(addr), sz, asg(dst))
        }

        Store { addr, val, .. } => {
            let sz = size_suffix(val.size);
            format!("{},{},={}", vn(val), vn(addr), sz)
        }
        Fence { .. } => String::new(),
        LoadLinked { dst, addr, .. } => {
            let sz = size_suffix(dst.size);
            format!("{},{},{}", vn(addr), sz, asg(dst))
        }
        StoreConditional {
            result, addr, val, ..
        } => {
            let sz = size_suffix(val.size);
            // Baseline LL/SC modeling: we only encode the success path in ESIL.
            // SC success is architecturally reported as 0 (non-zero means failure).
            match result {
                Some(dst) => format!("{},{},={},0,{}", vn(val), vn(addr), sz, asg(dst)),
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
            // `==` leaves nothing on the stack, so the branch condition has to
            // come from the zero flag it sets.
            format!(
                "{},{},{},{},{},==,$z,?{{,{},{},={},}}",
                vn(addr),
                sz,
                asg(dst),
                vn(expected),
                vn(dst),
                vn(replacement),
                vn(addr),
                sz
            )
        }
        LoadGuarded {
            dst, addr, guard, ..
        } => {
            let sz = size_suffix(dst.size);
            format!("{},?{{,{},{},{},}}", vn(guard), vn(addr), sz, asg(dst))
        }
        StoreGuarded {
            addr, val, guard, ..
        } => {
            let sz = size_suffix(val.size);
            format!("{},?{{,{},{},={},}}", vn(guard), vn(val), vn(addr), sz)
        }

        // ========== Integer Arithmetic ==========
        IntAdd { dst, a, b } => format!("{},{},+,{}", vn(b), vn(a), asg(dst)),
        IntSub { dst, a, b } => format!("{},{},-,{}", vn(b), vn(a), asg(dst)),
        IntMult { dst, a, b } => format!("{},{},*,{}", vn(b), vn(a), asg(dst)),
        IntDiv { dst, a, b } => format!("{},{},/,{}", vn(b), vn(a), asg(dst)),
        IntSDiv { dst, a, b } => format!("{},{},~/,{}", vn(b), vn(a), asg(dst)),
        IntRem { dst, a, b } => format!("{},{},%,{}", vn(b), vn(a), asg(dst)),
        IntSRem { dst, a, b } => format!("{},{},~%,{}", vn(b), vn(a), asg(dst)),
        IntNegate { dst, src } => format!("{},0,-,{}", vn(src), asg(dst)),

        // Carry/borrow operations. P-code defines these as self-contained
        // predicates over both operands, so they are built from an explicit
        // comparison rather than from flags an earlier instruction happened to
        // leave behind.
        IntCarry { dst, a, b } => {
            let bits = bit_width(a);
            // carry out of a + b is ((a + b) mod 2^n) <u a
            format!(
                "{},{},{},+,{},&,==,{},$b,{}",
                vn(a),
                vn(b),
                vn(a),
                mask_literal(bits),
                bits,
                asg(dst)
            )
        }
        IntSCarry { dst, a, b } => {
            let bits = bit_width(a);
            // signed overflow of a + b is set when both operands share a sign
            // that the sum does not: ~(a ^ b) & (a ^ (a + b)), sign bit taken
            format!(
                "{},{},{},^,{},^,{},{},+,{},^,&,>>,1,&,{}",
                bits - 1,
                vn(b),
                vn(a),
                mask_literal(bits),
                vn(b),
                vn(a),
                vn(a),
                asg(dst)
            )
        }
        IntSBorrow { dst, a, b } => {
            let bits = bit_width(a);
            format!(
                "{},{},{}",
                compare_prologue(&vn(a), &vn(b)),
                signed_overflow_terms(&vn(b), bits),
                asg(dst)
            )
        }

        // ========== Logical Operations ==========
        IntAnd { dst, a, b } => format!("{},{},&,{}", vn(b), vn(a), asg(dst)),
        IntOr { dst, a, b } => format!("{},{},|,{}", vn(b), vn(a), asg(dst)),
        IntXor { dst, a, b } => format!("{},{},^,{}", vn(b), vn(a), asg(dst)),
        // ESIL has no bitwise complement; `~` is sign extension. XOR with the
        // all-ones mask of the operand width is the same value.
        IntNot { dst, src } => format!(
            "{},{},^,{}",
            mask_literal(bit_width(src)),
            vn(src),
            asg(dst)
        ),

        // ========== Shift Operations ==========
        IntLeft { dst, a, b } => format!("{},{},<<,{}", vn(b), vn(a), asg(dst)),
        IntRight { dst, a, b } => format!("{},{},>>,{}", vn(b), vn(a), asg(dst)),
        IntSRight { dst, a, b } => format!("{},{},ASR,{}", vn(b), vn(a), asg(dst)),

        // ========== Comparison Operations ==========
        IntEqual { dst, a, b } => format!("{},$z,{}", compare_prologue(&vn(a), &vn(b)), asg(dst)),
        IntNotEqual { dst, a, b } => {
            format!("{},$z,!,{}", compare_prologue(&vn(a), &vn(b)), asg(dst))
        }
        IntLess { dst, a, b } => format!(
            "{},{},$b,{}",
            compare_prologue(&vn(a), &vn(b)),
            bit_width(a),
            asg(dst)
        ),
        IntLessEqual { dst, a, b } => format!(
            "{},{},$b,$z,|,{}",
            compare_prologue(&vn(a), &vn(b)),
            bit_width(a),
            asg(dst)
        ),
        IntSLess { dst, a, b } => {
            let bits = bit_width(a);
            format!(
                "{},{},$s,{},^,{}",
                compare_prologue(&vn(a), &vn(b)),
                bits - 1,
                signed_overflow_terms(&vn(b), bits),
                asg(dst)
            )
        }
        IntSLessEqual { dst, a, b } => {
            let bits = bit_width(a);
            // every flag is read before the first `^`, which overwrites the
            // comparison state `$z`, `$s` and `$o` all draw from
            format!(
                "{},$z,{},$s,{},^,^,|,{}",
                compare_prologue(&vn(a), &vn(b)),
                bits - 1,
                signed_overflow_terms(&vn(b), bits),
                asg(dst)
            )
        }

        // ========== Extension Operations ==========
        IntZExt { dst, src } => format!(
            "{},{},&,{}",
            mask_literal(bit_width(src)),
            vn(src),
            asg(dst)
        ),
        IntSExt { dst, src } => {
            format!("{},{},~,{}", bit_width(src), vn(src), asg(dst))
        }

        // ========== Boolean Operations ==========
        // P-code booleans are already 0 or 1, so the bitwise forms are exact
        // and ESIL has no dedicated logical connectives.
        BoolNot { dst, src } => format!("{},!,{}", vn(src), asg(dst)),
        BoolAnd { dst, a, b } => format!("{},{},&,{}", vn(b), vn(a), asg(dst)),
        BoolOr { dst, a, b } => format!("{},{},|,{}", vn(b), vn(a), asg(dst)),
        BoolXor { dst, a, b } => format!("{},{},^,{}", vn(b), vn(a), asg(dst)),

        // ========== Bit Manipulation ==========
        Piece { dst, hi, lo } => {
            // Concatenate: dst = (hi << lo.size*8) | lo
            let shift = (lo.size * 8).min(63);
            format!("{},{},<<,{},|,{}", shift, vn(hi), vn(lo), asg(dst))
        }

        Subpiece { dst, src, offset } => {
            // Extract: dst = (src >> offset*8) truncated to the destination
            let shift = (offset * 8).min(63);
            let keep = mask_literal(bit_width(dst));
            if shift > 0 {
                format!("{},{},>>,{},&,{}", shift, vn(src), keep, asg(dst))
            } else {
                format!("{},{},&,{}", keep, vn(src), asg(dst))
            }
        }

        // ESIL has no population count or count-leading-zeros operator, and
        // inventing one would be silently wrong rather than visibly missing.
        PopCount { .. } => "TODO".to_string(),
        Lzcount { .. } => "TODO".to_string(),

        // ========== Control Flow ==========
        // A p-code branch target names an address, not the memory at it.
        Branch { target } => format!("{},pc,=", vaddr(target)),

        CBranch { target, cond } => {
            // Conditional branch: if cond then goto target
            format!("{},?{{,{},pc,=,}}", vn(cond), vaddr(target))
        }

        BranchInd { target } => format!("{},pc,=", vn(target)),

        // Sleigh already emits the architectural side effects of a call and a
        // return - the return-address push, the link register write, the stack
        // pop - as ordinary p-code. Re-synthesizing them here pushed the return
        // address twice and moved the stack pointer twice per call.
        Call { target } => format!("{},pc,=", vaddr(target)),
        CallInd { target } => format!("{},pc,=", vn(target)),
        Return { target } => format!("{},pc,=", vn(target)),

        // ========== Floating Point ==========
        FloatAdd { dst, a, b } => format!("{},{},F+,{}", vn(b), vn(a), asg(dst)),
        FloatSub { dst, a, b } => format!("{},{},F-,{}", vn(b), vn(a), asg(dst)),
        FloatMult { dst, a, b } => format!("{},{},F*,{}", vn(b), vn(a), asg(dst)),
        FloatDiv { dst, a, b } => format!("{},{},F/,{}", vn(b), vn(a), asg(dst)),
        FloatNeg { dst, src } => format!("{},-F,{}", vn(src), asg(dst)),
        FloatSqrt { dst, src } => format!("{},SQRT,{}", vn(src), asg(dst)),
        FloatCeil { dst, src } => format!("{},CEIL,{}", vn(src), asg(dst)),
        FloatFloor { dst, src } => format!("{},FLOOR,{}", vn(src), asg(dst)),
        FloatRound { dst, src } => format!("{},ROUND,{}", vn(src), asg(dst)),
        // ESIL models neither absolute value nor NaN classification.
        FloatAbs { .. } => "TODO".to_string(),
        FloatNaN { .. } => "TODO".to_string(),
        FloatEqual { dst, a, b } => format!("{},{},F==,{}", vn(b), vn(a), asg(dst)),
        FloatNotEqual { dst, a, b } => format!("{},{},F!=,{}", vn(b), vn(a), asg(dst)),
        FloatLess { dst, a, b } => format!("{},{},F<,{}", vn(b), vn(a), asg(dst)),
        FloatLessEqual { dst, a, b } => format!("{},{},F<=,{}", vn(b), vn(a), asg(dst)),
        Int2Float { dst, src } => format!("{},I2D,{}", vn(src), asg(dst)),
        Float2Int { dst, src } => format!("{},D2I,{}", vn(src), asg(dst)),
        // ESIL's F2D/D2F take an explicit format operand this op does not carry.
        FloatFloat { .. } => "TODO".to_string(),
        Trunc { dst, src } => format!("{},D2I,{}", vn(src), asg(dst)),

        // ========== Special Operations ==========
        CallOther {
            output,
            userop,
            inputs,
        } => format_callother_esil(disasm, output, *userop, inputs),

        Nop => String::new(),
        Unimplemented => "TODO".to_string(),
        CpuId { .. } => "TODO".to_string(),
        Breakpoint => "BREAK".to_string(),

        // Analysis operations (typically not in raw P-code from disassembly).
        // A phi has no ESIL spelling; there is no single value to assign.
        Multiequal { .. } => "TODO".to_string(),

        Indirect { dst, src, .. } => format!("{},{}", vn(src), asg(dst)),

        PtrAdd {
            dst,
            base,
            index,
            element_size,
        } => {
            format!(
                "{},{},*,{},+,{}",
                element_size,
                vn(index),
                vn(base),
                asg(dst)
            )
        }

        PtrSub {
            dst,
            base,
            index,
            element_size,
        } => {
            format!(
                "{},{},*,{},-,{}",
                element_size,
                vn(index),
                vn(base),
                asg(dst)
            )
        }

        SegmentOp {
            dst,
            segment,
            offset,
        } => {
            // Segment:offset calculation (x86 real mode style)
            format!("4,{},<<,{},+,{}", vn(segment), vn(offset), asg(dst))
        }

        New { .. } => "TODO".to_string(),
        Cast { dst, src } => format!("{},{}", vn(src), asg(dst)),

        Extract { dst, src, position } => {
            format!("{},{},>>,{}", vn(position), vn(src), asg(dst))
        }

        Insert {
            dst,
            src,
            value,
            position,
        } => {
            // Insert value into src at position
            format!(
                "{},{},<<,{},|,{}",
                vn(position),
                vn(value),
                vn(src),
                asg(dst)
            )
        }
        Select {
            dst,
            cond,
            if_true,
            if_false,
        } => format!(
            "{},?{{,{},{},}}{{,{},{},}}",
            vn(cond),
            vn(if_true),
            asg(dst),
            vn(if_false),
            asg(dst)
        ),
    }
}

fn format_callother_esil(
    disasm: &Disassembler,
    output: &Option<r2il::Varnode>,
    userop: u32,
    inputs: &[r2il::Varnode],
) -> String {
    let vn = |v: &r2il::Varnode| disasm.format_varnode(v).to_lowercase();
    let args: Vec<String> = inputs.iter().map(&vn).collect();
    let args_str = args.join(",");
    match output {
        Some(dst) => format!("{},CALLOTHER({}),{},=", args_str, userop, vn(dst)),
        None => format!("{},CALLOTHER({})", args_str, userop),
    }
}

#[cfg(test)]
mod tests {
    use super::{format_op, op_to_esil};
    use crate::Disassembler;
    use r2il::{R2ILOp, Varnode};

    fn x86_64() -> Disassembler {
        Disassembler::from_sla(
            sleigh_config::processor_x86::SLA_X86_64,
            sleigh_config::processor_x86::PSPEC_X86_64,
            "x86-64",
        )
        .expect("x86-64 disassembler")
    }

    fn esil(op: &R2ILOp) -> String {
        op_to_esil(&x86_64(), op)
    }

    /// The last operand pushed is the left-hand side, so `a - b` has to place
    /// `b` first. Emitting `a,b,-` computed `b - a`.
    #[test]
    fn non_commutative_arithmetic_puts_the_left_operand_last() {
        let dst = Varnode::unique(0x100, 4);
        let a = Varnode::unique(0x200, 4);
        let b = Varnode::constant(3, 4);
        assert_eq!(
            esil(&R2ILOp::IntSub {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone()
            }),
            "0x3,tmp:0x200,-,tmp:0x100,="
        );
        assert_eq!(
            esil(&R2ILOp::IntDiv {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone()
            }),
            "0x3,tmp:0x200,/,tmp:0x100,="
        );
        assert_eq!(
            esil(&R2ILOp::IntSRight { dst, a, b }),
            "0x3,tmp:0x200,ASR,tmp:0x100,="
        );
    }

    /// `>>>`, `<$`, `<=$`, `~~`, `&&`, `||`, `^^`, `POPCOUNT` and `CLZ` are not
    /// radare2 ESIL operators; emitting them left the expression unevaluated.
    #[test]
    fn only_operators_radare2_defines_are_emitted() {
        const DEFINED: &[&str] = &[
            "+", "-", "*", "/", "%", "~/", "~%", "&", "|", "^", "!", "<<", ">>", "ASR", "ROR",
            "ROL", "~", "==", "=", ":=", "?{", "}", "}{", "$z", "$c", "$b", "$s", "$o", "$p",
            "TODO", "BREAK", "F+", "F-", "F*", "F/", "F==", "F!=", "F<", "F<=", "-F", "SQRT",
            "CEIL", "FLOOR", "ROUND", "I2D", "D2I",
        ];
        let dst = Varnode::unique(0x10, 4);
        let src = Varnode::unique(0x20, 4);
        let a = Varnode::unique(0x30, 4);
        let b = Varnode::unique(0x40, 4);
        let ops = [
            R2ILOp::IntSRight {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::IntSLess {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::IntSLessEqual {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::IntLess {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::IntLessEqual {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::IntEqual {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::IntNotEqual {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::IntCarry {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::IntSCarry {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::IntSBorrow {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::IntNot {
                dst: dst.clone(),
                src: src.clone(),
            },
            R2ILOp::IntSExt {
                dst: dst.clone(),
                src: src.clone(),
            },
            R2ILOp::IntZExt {
                dst: dst.clone(),
                src: src.clone(),
            },
            R2ILOp::BoolAnd {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::BoolOr {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::BoolXor {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone(),
            },
            R2ILOp::PopCount {
                dst: dst.clone(),
                src: src.clone(),
            },
            R2ILOp::Lzcount {
                dst: dst.clone(),
                src: src.clone(),
            },
            R2ILOp::FloatSqrt {
                dst: dst.clone(),
                src: src.clone(),
            },
            R2ILOp::FloatNeg {
                dst: dst.clone(),
                src: src.clone(),
            },
            R2ILOp::FloatAbs {
                dst: dst.clone(),
                src: src.clone(),
            },
            R2ILOp::Int2Float {
                dst: dst.clone(),
                src: src.clone(),
            },
            R2ILOp::Float2Int {
                dst: dst.clone(),
                src: src.clone(),
            },
            R2ILOp::Trunc {
                dst: dst.clone(),
                src: src.clone(),
            },
            R2ILOp::Unimplemented,
        ];
        let disassembler = x86_64();
        for op in &ops {
            for token in op_to_esil(&disassembler, op).split(',') {
                let is_operand = token.is_empty()
                    || token.starts_with("0x")
                    || token.starts_with("tmp:")
                    || token.chars().all(|c| c.is_ascii_digit())
                    || token.starts_with('[')
                    || token.starts_with("=[");
                assert!(
                    is_operand || DEFINED.contains(&token),
                    "{op:?} emitted undefined ESIL token {token:?}"
                );
            }
        }
    }

    /// Verified against radare2's own evaluator over every pairing of the
    /// boundary values for the width: `ae <expr>` agrees with the P-code
    /// definition on all of them.
    #[test]
    fn comparisons_read_flags_from_an_explicit_compare() {
        let dst = Varnode::unique(0x10, 1);
        let a = Varnode::unique(0x20, 4);
        let b = Varnode::unique(0x30, 4);
        assert_eq!(
            esil(&R2ILOp::IntLess {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone()
            }),
            "tmp:0x30,tmp:0x20,==,32,$b,tmp:0x10,="
        );
        assert_eq!(
            esil(&R2ILOp::IntEqual {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone()
            }),
            "tmp:0x30,tmp:0x20,==,$z,tmp:0x10,="
        );
        assert_eq!(
            esil(&R2ILOp::IntSLess {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone()
            }),
            "tmp:0x30,tmp:0x20,==,31,$s,31,$o,0x80000000,tmp:0x30,-,!,^,^,tmp:0x10,="
        );
        assert_eq!(
            esil(&R2ILOp::IntSBorrow { dst, a, b }),
            "tmp:0x30,tmp:0x20,==,31,$o,0x80000000,tmp:0x30,-,!,^,tmp:0x10,="
        );
    }

    /// A branch target is an address. Rendering the ram varnode as a value made
    /// `jmp 0x100000340` load eight bytes from that address and jump there.
    #[test]
    fn branch_targets_are_addresses_not_loads() {
        assert_eq!(
            esil(&R2ILOp::Branch {
                target: Varnode::ram(0x100000340, 8)
            }),
            "0x100000340,pc,="
        );
        assert_eq!(
            esil(&R2ILOp::Call {
                target: Varnode::ram(0x1000004c0, 8)
            }),
            "0x1000004c0,pc,="
        );
    }

    /// Sleigh already emits the return-address push and the stack pop as
    /// ordinary p-code; the lifter must not add a second copy.
    #[test]
    fn calls_and_returns_do_not_restate_the_stack_effects() {
        for op in [
            R2ILOp::Call {
                target: Varnode::ram(0x1000, 8),
            },
            R2ILOp::CallInd {
                target: Varnode::register(0x10, 8),
            },
            R2ILOp::Return {
                target: Varnode::register(0x10, 8),
            },
        ] {
            let esil = esil(&op);
            assert!(!esil.contains("rsp"), "{op:?} restated the stack: {esil}");
            assert!(!esil.contains("=[8]"), "{op:?} restated the push: {esil}");
            assert!(esil.ends_with("pc,="), "{op:?} must set pc: {esil}");
        }
    }

    #[test]
    fn callother_rendering_is_numeric_and_ambient_independent() {
        let disassembler = Disassembler::from_sla(
            sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
            sleigh_config::processor_aarch64::PSPEC_AARCH64,
            "aarch64",
        )
        .expect("AArch64 disassembler");
        let op = R2ILOp::CallOther {
            output: None,
            userop: u32::MAX,
            inputs: vec![Varnode::constant(1, 8)],
        };

        assert_eq!(
            format_op(&disassembler, &op),
            "CallOther { output: none, userop: 4294967295, inputs: [0x1] }"
        );
        assert_eq!(op_to_esil(&disassembler, &op), "0x1,CALLOTHER(4294967295)");
    }
}
