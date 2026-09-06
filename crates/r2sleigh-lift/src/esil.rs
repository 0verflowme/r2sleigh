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

/// Population count as a pure ESIL expression.
///
/// radare2 has no popcount operator, but it has `DUP` and `SWAP`, so the usual
/// SWAR reduction can be written out. Doing it this way keeps the operand
/// expression written once, which matters because the operand may itself be a
/// spliced temporary. Checked against `ae` for zero, one, all-ones, both sign
/// boundaries and mixed patterns at 64 bits.
fn popcount_terms() -> &'static str {
    concat!(
        "DUP,1,SWAP,>>,0x5555555555555555,&,SWAP,-,",
        "DUP,2,SWAP,>>,0x3333333333333333,&,SWAP,0x3333333333333333,&,+,",
        "DUP,4,SWAP,>>,+,0x0f0f0f0f0f0f0f0f,&,",
        "0x101010101010101,*,56,SWAP,>>"
    )
}

/// Smear the highest set bit down over every lower bit, so that a population
/// count of the result gives the index of that bit.
fn bit_smear_terms() -> &'static str {
    concat!(
        "DUP,1,SWAP,>>,|,DUP,2,SWAP,>>,|,DUP,4,SWAP,>>,|,",
        "DUP,8,SWAP,>>,|,DUP,16,SWAP,>>,|,DUP,32,SWAP,>>,|"
    )
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

/// What one p-code operation contributes to an instruction's ESIL.
///
/// The split matters because ESIL has no name for Sleigh's unique space. A
/// `Value` can be spliced into whoever reads it, which is the only way a
/// temporary ever disappears; an `Effect` has to stay where it is.
#[derive(Debug, Clone)]
pub enum OpEsil {
    /// A pure computation that leaves its result in `dst`.
    Value {
        dst: r2il::Varnode,
        /// Tokens that push the result, with no trailing assignment.
        expr: String,
    },
    /// A statement whose position in the sequence is part of its meaning.
    Effect(String),
    /// The operation contributes nothing.
    Empty,
    /// radare2 models nothing equivalent.
    Unmodelled,
}

impl OpEsil {
    /// Render standalone, assigning any value to its destination.
    fn render(&self, disasm: &Disassembler) -> String {
        match self {
            OpEsil::Value { dst, expr } => {
                let target = match dst.space {
                    r2il::SpaceId::Ram => {
                        format!("0x{:x},=[{}]", dst.offset, dst.size.clamp(1, 8))
                    }
                    _ => format!("{},=", disasm.format_varnode(dst).to_lowercase()),
                };
                format!("{expr},{target}")
            }
            OpEsil::Effect(text) => text.clone(),
            OpEsil::Empty => String::new(),
            OpEsil::Unmodelled => "TODO".to_string(),
        }
    }
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
pub fn op_esil(disasm: &Disassembler, op: &R2ILOp) -> OpEsil {
    op_esil_with(disasm, op, &Substitutions::default())
}

/// The value a unique-space varnode holds, as the tokens that recompute it.
///
/// Kept with what it reads so the block emitter can tell when an intervening
/// write makes the expression no longer safe to move.
#[derive(Debug, Clone)]
struct Pending {
    expr: String,
    /// Each storage the expression reads, paired with the generation of the
    /// value it needs. Carrying the generation from where the expression was
    /// built is what lets it be spliced past a later write to that storage.
    reads: Vec<(r2il::Varnode, usize)>,
    reads_memory: bool,
}

/// Values produced so far, newest last.
///
/// Every value is forwarded, not just the unique-space ones. Sleigh saves a
/// register into a temporary, overwrites the register, and then computes a flag
/// from both the saved copy and the new value; reading that flag's operands
/// back out of registers cannot reproduce it in any order. Forwarding the
/// producing expression instead makes each operand refer to the generation it
/// was written from, so ordering stops mattering for reads.
#[derive(Debug, Default)]
struct Substitutions {
    writers: Vec<Writer>,
    /// Set when a read found no live definition, which makes the instruction
    /// inexpressible rather than subtly wrong.
    broken: std::cell::Cell<bool>,
    /// What the operands rendered so far read. A `None` generation means the
    /// operand was read directly and takes whatever generation is current where
    /// the reading operation sits.
    used: std::cell::RefCell<Vec<(r2il::Varnode, Option<usize>)>>,
    used_memory: std::cell::Cell<bool>,
}

/// A write performed by an earlier operation of the same instruction.
#[derive(Debug, Clone)]
struct Writer {
    storage: r2il::Varnode,
    /// P-code step that performed the write, counting from one.
    generation: usize,
    /// The expression that produced it, when the write came from a pure value.
    /// A write with no expression - a store, or something unmodelled - can only
    /// be read back out of the register it landed in.
    value: Option<Pending>,
}

/// Beyond this many tokens a forwarded expression is left as a register read
/// instead, so that a long p-code sequence cannot expand geometrically. The
/// read then constrains the order, which is the ordinary case.
const MAX_FORWARDED_TOKENS: usize = 4096;

impl Substitutions {
    /// The most recent write covering `v`, if any.
    fn writer_for(&self, v: &r2il::Varnode) -> Option<&Writer> {
        self.writers
            .iter()
            .rev()
            .find(|writer| overlaps(&writer.storage, v))
    }

    fn begin_op(&self) {
        self.used.borrow_mut().clear();
        self.used_memory.set(false);
    }

    fn note_read(&self, v: &r2il::Varnode) {
        if v.space == r2il::SpaceId::Ram {
            self.used_memory.set(true);
        }
        self.used.borrow_mut().push((v.clone(), None));
    }
}

/// Whether two varnodes name storage that shares at least one byte.
fn overlaps(a: &r2il::Varnode, b: &r2il::Varnode) -> bool {
    a.space == b.space
        && a.offset < b.offset + u64::from(b.size.max(1))
        && b.offset < a.offset + u64::from(a.size.max(1))
}

fn op_esil_with(disasm: &Disassembler, op: &R2ILOp, subst: &Substitutions) -> OpEsil {
    use r2il::R2ILOp::*;

    subst.begin_op();

    let value = |dst: &r2il::Varnode, expr: String| OpEsil::Value {
        dst: dst.clone(),
        expr,
    };
    let effect = |text: String| OpEsil::Effect(text);
    // The processor spec names the program counter; it is `RIP` on x86-64 and
    // `EIP` on x86, not the literal `pc` ESIL would otherwise be handed.
    let pc = disasm.program_counter().to_ascii_lowercase();

    // Helper to format varnode as a lowercase ESIL operand. A ram varnode names
    // a memory cell, so reading its value is a load, not a bare address. A
    // unique renders as the expression that produced it, because radare2 has no
    // name for Sleigh's temporaries.
    let vn = |v: &r2il::Varnode| -> String {
        let writer = subst.writer_for(v);
        let forwardable = writer.and_then(|writer| {
            let pending = writer.value.as_ref()?;
            // Only an exact-width write can stand in for the read; a partial
            // overlap would need masking this layer does not know how to build.
            (writer.storage.offset == v.offset
                && writer.storage.size == v.size
                && pending.expr.len() <= MAX_FORWARDED_TOKENS)
                .then_some(pending)
        });
        if let Some(pending) = forwardable {
            subst.used.borrow_mut().extend(
                pending
                    .reads
                    .iter()
                    .map(|(read, generation)| (read.clone(), Some(*generation))),
            );
            if pending.reads_memory {
                subst.used_memory.set(true);
            }
            return pending.expr.clone();
        }
        if v.space == r2il::SpaceId::Unique {
            // A temporary has no register to fall back on.
            subst.broken.set(true);
            return "TODO".to_string();
        }
        subst.note_read(v);
        match v.space {
            r2il::SpaceId::Ram => format!("0x{:x},[{}]", v.offset, v.size.clamp(1, 8)),
            _ => disasm.format_varnode(v).to_lowercase(),
        }
    };

    // The same varnode used as an address rather than as a value.
    let vaddr = |v: &r2il::Varnode| -> String {
        if v.space == r2il::SpaceId::Unique || subst.writer_for(v).is_some() {
            return vn(v);
        }
        subst.note_read(v);
        match v.space {
            r2il::SpaceId::Ram => format!("0x{:x}", v.offset),
            _ => disasm.format_varnode(v).to_lowercase(),
        }
    };

    // Assignment suffix for a destination varnode, for the effect arms that
    // have to spell the write out themselves.
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
        Copy { dst, src } => value(dst, vn(src)),

        Load { dst, addr, .. } => {
            let sz = size_suffix(dst.size);
            value(dst, format!("{},{}", vn(addr), sz))
        }

        Store { addr, val, .. } => {
            let sz = size_suffix(val.size);
            effect(format!("{},{},={}", vn(val), vn(addr), sz))
        }
        Fence { .. } => OpEsil::Empty,
        LoadLinked { dst, addr, .. } => {
            let sz = size_suffix(dst.size);
            value(dst, format!("{},{}", vn(addr), sz))
        }
        StoreConditional {
            result, addr, val, ..
        } => {
            let sz = size_suffix(val.size);
            // Baseline LL/SC modeling: we only encode the success path in ESIL.
            // SC success is architecturally reported as 0 (non-zero means failure).
            match result {
                Some(dst) => effect(format!("{},{},={},0,{}", vn(val), vn(addr), sz, asg(dst))),
                None => effect(format!("{},{},={}", vn(val), vn(addr), sz)),
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
            effect(format!(
                "{},{},{},{},{},==,$z,?{{,{},{},={},}}",
                vn(addr),
                sz,
                asg(dst),
                vn(expected),
                vn(dst),
                vn(replacement),
                vn(addr),
                sz
            ))
        }
        LoadGuarded {
            dst, addr, guard, ..
        } => {
            let sz = size_suffix(dst.size);
            effect(format!(
                "{},?{{,{},{},{},}}",
                vn(guard),
                vn(addr),
                sz,
                asg(dst)
            ))
        }
        StoreGuarded {
            addr, val, guard, ..
        } => {
            let sz = size_suffix(val.size);
            effect(format!(
                "{},?{{,{},{},={},}}",
                vn(guard),
                vn(val),
                vn(addr),
                sz
            ))
        }

        // ========== Integer Arithmetic ==========
        IntAdd { dst, a, b } => value(dst, format!("{},{},+", vn(b), vn(a))),
        IntSub { dst, a, b } => value(dst, format!("{},{},-", vn(b), vn(a))),
        IntMult { dst, a, b } => value(dst, format!("{},{},*", vn(b), vn(a))),
        IntDiv { dst, a, b } => value(dst, format!("{},{},/", vn(b), vn(a))),
        IntSDiv { dst, a, b } => value(dst, format!("{},{},~/", vn(b), vn(a))),
        IntRem { dst, a, b } => value(dst, format!("{},{},%", vn(b), vn(a))),
        IntSRem { dst, a, b } => value(dst, format!("{},{},~%", vn(b), vn(a))),
        IntNegate { dst, src } => value(dst, format!("{},0,-", vn(src))),

        // Carry/borrow operations. P-code defines these as self-contained
        // predicates over both operands, so they are built from an explicit
        // comparison rather than from flags an earlier instruction happened to
        // leave behind.
        IntCarry { dst, a, b } => {
            let bits = bit_width(a);
            // carry out of a + b is ((a + b) mod 2^n) <u a
            value(
                dst,
                format!(
                    "{},{},{},+,{},&,==,{},$b",
                    vn(a),
                    vn(b),
                    vn(a),
                    mask_literal(bits),
                    bits
                ),
            )
        }
        IntSCarry { dst, a, b } => {
            let bits = bit_width(a);
            // signed overflow of a + b is set when both operands share a sign
            // that the sum does not: ~(a ^ b) & (a ^ (a + b)), sign bit taken
            value(
                dst,
                format!(
                    "{},{},{},^,{},^,{},{},+,{},^,&,>>,1,&",
                    bits - 1,
                    vn(b),
                    vn(a),
                    mask_literal(bits),
                    vn(b),
                    vn(a),
                    vn(a)
                ),
            )
        }
        IntSBorrow { dst, a, b } => {
            let bits = bit_width(a);
            value(
                dst,
                format!(
                    "{},{}",
                    compare_prologue(&vn(a), &vn(b)),
                    signed_overflow_terms(&vn(b), bits)
                ),
            )
        }

        // ========== Logical Operations ==========
        IntAnd { dst, a, b } => value(dst, format!("{},{},&", vn(b), vn(a))),
        IntOr { dst, a, b } => value(dst, format!("{},{},|", vn(b), vn(a))),
        IntXor { dst, a, b } => value(dst, format!("{},{},^", vn(b), vn(a))),
        // ESIL has no bitwise complement; `~` is sign extension. XOR with the
        // all-ones mask of the operand width is the same value.
        IntNot { dst, src } => value(
            dst,
            format!("{},{},^", mask_literal(bit_width(src)), vn(src)),
        ),

        // ========== Shift Operations ==========
        IntLeft { dst, a, b } => value(dst, format!("{},{},<<", vn(b), vn(a))),
        IntRight { dst, a, b } => value(dst, format!("{},{},>>", vn(b), vn(a))),
        IntSRight { dst, a, b } => value(dst, format!("{},{},ASR", vn(b), vn(a))),

        // ========== Comparison Operations ==========
        IntEqual { dst, a, b } => value(dst, format!("{},$z", compare_prologue(&vn(a), &vn(b)))),
        IntNotEqual { dst, a, b } => {
            value(dst, format!("{},$z,!", compare_prologue(&vn(a), &vn(b))))
        }
        IntLess { dst, a, b } => value(
            dst,
            format!("{},{},$b", compare_prologue(&vn(a), &vn(b)), bit_width(a)),
        ),
        IntLessEqual { dst, a, b } => value(
            dst,
            format!(
                "{},{},$b,$z,|",
                compare_prologue(&vn(a), &vn(b)),
                bit_width(a)
            ),
        ),
        IntSLess { dst, a, b } => {
            let bits = bit_width(a);
            value(
                dst,
                format!(
                    "{},{},$s,{},^",
                    compare_prologue(&vn(a), &vn(b)),
                    bits - 1,
                    signed_overflow_terms(&vn(b), bits)
                ),
            )
        }
        IntSLessEqual { dst, a, b } => {
            let bits = bit_width(a);
            // every flag is read before the first `^`, which overwrites the
            // comparison state `$z`, `$s` and `$o` all draw from
            value(
                dst,
                format!(
                    "{},$z,{},$s,{},^,^,|",
                    compare_prologue(&vn(a), &vn(b)),
                    bits - 1,
                    signed_overflow_terms(&vn(b), bits)
                ),
            )
        }

        // ========== Extension Operations ==========
        IntZExt { dst, src } => value(
            dst,
            format!("{},{},&", mask_literal(bit_width(src)), vn(src)),
        ),
        IntSExt { dst, src } => value(dst, format!("{},{},~", bit_width(src), vn(src))),

        // ========== Boolean Operations ==========
        // P-code booleans are already 0 or 1, so the bitwise forms are exact
        // and ESIL has no dedicated logical connectives.
        BoolNot { dst, src } => value(dst, format!("{},!", vn(src))),
        BoolAnd { dst, a, b } => value(dst, format!("{},{},&", vn(b), vn(a))),
        BoolOr { dst, a, b } => value(dst, format!("{},{},|", vn(b), vn(a))),
        BoolXor { dst, a, b } => value(dst, format!("{},{},^", vn(b), vn(a))),

        // ========== Bit Manipulation ==========
        Piece { dst, hi, lo } => {
            // Concatenate: dst = (hi << lo.size*8) | lo
            let shift = (lo.size * 8).min(63);
            value(dst, format!("{},{},<<,{},|", shift, vn(hi), vn(lo)))
        }

        Subpiece { dst, src, offset } => {
            // Extract: dst = (src >> offset*8) truncated to the destination
            let shift = (offset * 8).min(63);
            let keep = mask_literal(bit_width(dst));
            if shift > 0 {
                value(dst, format!("{},{},>>,{},&", shift, vn(src), keep))
            } else {
                value(dst, format!("{},{},&", keep, vn(src)))
            }
        }

        PopCount { dst, src } => value(
            dst,
            format!(
                "{},{},&,{}",
                mask_literal(bit_width(src)),
                vn(src),
                popcount_terms()
            ),
        ),
        // Leading zeros over the operand's own width: smear the top set bit
        // down, count what is left, and subtract from the width.
        Lzcount { dst, src } => {
            let bits = bit_width(src);
            value(
                dst,
                format!(
                    "{},{},&,{},{},{},-",
                    mask_literal(bits),
                    vn(src),
                    bit_smear_terms(),
                    popcount_terms(),
                    bits
                ),
            )
        }

        // ========== Control Flow ==========
        // A p-code branch target names an address, not the memory at it.
        Branch { target } => effect(format!("{},{pc},=", vaddr(target))),

        CBranch { target, cond } => {
            // Conditional branch: if cond then goto target
            effect(format!("{},?{{,{},{pc},=,}}", vn(cond), vaddr(target)))
        }

        BranchInd { target } => effect(format!("{},{pc},=", vn(target))),

        // Sleigh already emits the architectural side effects of a call and a
        // return - the return-address push, the link register write, the stack
        // pop - as ordinary p-code. Re-synthesizing them here pushed the return
        // address twice and moved the stack pointer twice per call.
        Call { target } => effect(format!("{},{pc},=", vaddr(target))),
        CallInd { target } => effect(format!("{},{pc},=", vn(target))),
        Return { target } => effect(format!("{},{pc},=", vn(target))),

        // ========== Floating Point ==========
        FloatAdd { dst, a, b } => value(dst, format!("{},{},F+", vn(b), vn(a))),
        FloatSub { dst, a, b } => value(dst, format!("{},{},F-", vn(b), vn(a))),
        FloatMult { dst, a, b } => value(dst, format!("{},{},F*", vn(b), vn(a))),
        FloatDiv { dst, a, b } => value(dst, format!("{},{},F/", vn(b), vn(a))),
        FloatNeg { dst, src } => value(dst, format!("{},-F", vn(src))),
        FloatSqrt { dst, src } => value(dst, format!("{},SQRT", vn(src))),
        FloatCeil { dst, src } => value(dst, format!("{},CEIL", vn(src))),
        FloatFloor { dst, src } => value(dst, format!("{},FLOOR", vn(src))),
        FloatRound { dst, src } => value(dst, format!("{},ROUND", vn(src))),
        // ESIL models neither absolute value nor NaN classification.
        FloatAbs { .. } => OpEsil::Unmodelled,
        FloatNaN { .. } => OpEsil::Unmodelled,
        FloatEqual { dst, a, b } => value(dst, format!("{},{},F==", vn(b), vn(a))),
        FloatNotEqual { dst, a, b } => value(dst, format!("{},{},F!=", vn(b), vn(a))),
        FloatLess { dst, a, b } => value(dst, format!("{},{},F<", vn(b), vn(a))),
        FloatLessEqual { dst, a, b } => value(dst, format!("{},{},F<=", vn(b), vn(a))),
        Int2Float { dst, src } => value(dst, format!("{},I2D", vn(src))),
        Float2Int { dst, src } => value(dst, format!("{},D2I", vn(src))),
        // ESIL's F2D/D2F take an explicit format operand this op does not carry.
        FloatFloat { .. } => OpEsil::Unmodelled,
        Trunc { dst, src } => value(dst, format!("{},D2I", vn(src))),

        // ========== Special Operations ==========
        CallOther {
            output,
            userop,
            inputs,
        } => {
            // Rendered here rather than in a helper of its own, so the operands
            // go through the same substitution as every other operand.
            let args = inputs.iter().map(&vn).collect::<Vec<_>>().join(",");
            match output {
                Some(dst) => effect(format!("{},CALLOTHER({}),{}", args, userop, asg(dst))),
                None => effect(format!("{},CALLOTHER({})", args, userop)),
            }
        }

        Nop => OpEsil::Empty,
        Unimplemented => OpEsil::Unmodelled,
        CpuId { .. } => OpEsil::Unmodelled,
        Breakpoint => effect("BREAK".to_string()),

        // Analysis operations (typically not in raw P-code from disassembly).
        // A phi has no ESIL spelling; there is no single value to assign.
        Multiequal { .. } => OpEsil::Unmodelled,

        Indirect { dst, src, .. } => value(dst, vn(src)),

        PtrAdd {
            dst,
            base,
            index,
            element_size,
        } => value(
            dst,
            format!("{},{},*,{},+", element_size, vn(index), vn(base)),
        ),

        PtrSub {
            dst,
            base,
            index,
            element_size,
        } => value(
            dst,
            format!("{},{},*,{},-", element_size, vn(index), vn(base)),
        ),

        SegmentOp {
            dst,
            segment,
            offset,
        } => {
            // Segment:offset calculation (x86 real mode style)
            value(dst, format!("4,{},<<,{},+", vn(segment), vn(offset)))
        }

        New { .. } => OpEsil::Unmodelled,
        Cast { dst, src } => value(dst, vn(src)),

        Extract { dst, src, position } => value(dst, format!("{},{},>>", vn(position), vn(src))),

        Insert {
            dst,
            src,
            value,
            position,
        } => {
            // Insert value into src at position
            OpEsil::Value {
                dst: dst.clone(),
                expr: format!("{},{},<<,{},|", vn(position), vn(value), vn(src)),
            }
        }
        Select {
            dst,
            cond,
            if_true,
            if_false,
        } => effect(format!(
            "{},?{{,{},{},}}{{,{},{},}}",
            vn(cond),
            vn(if_true),
            asg(dst),
            vn(if_false),
            asg(dst)
        )),
    }
}

/// Render a whole instruction's p-code as one ESIL string.
///
/// Two things make this a block-level job rather than a per-operation one.
///
/// radare2 stops evaluating an ESIL string at the first `;` (`eval_word` in
/// libr/esil/esil.c returns to the caller on that separator), so joining
/// operations with `;` executes the first one and discards the rest. Operations
/// are joined with `,`.
///
/// And an ESIL operand is either a number or a register name; there is no
/// spelling for Sleigh's unique space, so `tmp:0x1234` fails to classify and
/// every operation carrying one is dropped. Each temporary is therefore spliced
/// into whoever reads it. A temporary whose defining expression an intervening
/// write has invalidated cannot be spliced, and the instruction is reported as
/// unmodelled rather than emitted with the wrong value.
pub fn block_to_esil(disasm: &Disassembler, block: &r2il::R2ILBlock) -> String {
    let mut subst = Substitutions::default();
    let mut planned: Vec<Statement> = Vec::new();
    // Set when some part of the instruction could not be expressed. The rest is
    // still emitted: dropping an effect leaves a value stale, while emitting one
    // built on a temporary radare2 cannot name would make it wrong.
    let mut partial = false;
    // Memory is tracked as one storage; register generations live with the
    // writers the substitution table already keeps.
    let mut last_memory_write = 0usize;

    for (index, op) in block.ops.iter().enumerate() {
        let step = index + 1;
        subst.broken.set(false);
        let form = op_esil_with(disasm, op, &subst);
        let unresolved = subst.broken.get();
        let reads = subst.used.borrow().clone();
        let reads_memory = subst.used_memory.get() || reads_memory_directly(op);

        // The generation each operand needs. A forwarded operand carries the
        // generation it was built from; a plain register read takes whatever is
        // current where this operation sits.
        let mut needs: Vec<(r2il::Varnode, usize)> = Vec::new();
        for (read, carried) in &reads {
            let generation = carried.unwrap_or_else(|| {
                subst
                    .writer_for(read)
                    .map(|writer| writer.generation)
                    .unwrap_or(0)
            });
            needs.push((read.clone(), generation));
        }
        let needs_memory = if reads_memory { last_memory_write } else { 0 };

        let written = op.output().cloned();
        let mut produced: Option<Pending> = None;

        match form {
            OpEsil::Unmodelled => partial = true,
            _ if unresolved => partial = true,
            OpEsil::Value { dst, expr } => {
                produced = Some(Pending {
                    expr: expr.clone(),
                    reads: needs.clone(),
                    reads_memory,
                });
                if dst.space != r2il::SpaceId::Unique {
                    planned.push(Statement {
                        text: OpEsil::Value {
                            dst: dst.clone(),
                            expr: expr.clone(),
                        }
                        .render(disasm),
                        split: Some((expr, assignment_target(disasm, &dst))),
                        generation: step,
                        needs,
                        reads_memory,
                        needs_memory,
                        writes: Some(dst),
                        writes_memory: writes_memory(op),
                    });
                }
            }
            OpEsil::Effect(text) => planned.push(Statement {
                text,
                split: None,
                generation: step,
                needs,
                reads_memory,
                needs_memory,
                writes: op
                    .output()
                    .filter(|v| v.space != r2il::SpaceId::Unique)
                    .cloned(),
                writes_memory: writes_memory(op),
            }),
            OpEsil::Empty => {}
        }

        if let Some(storage) = written {
            subst.writers.push(Writer {
                storage,
                generation: step,
                value: produced,
            });
        }
        if writes_memory(op) {
            last_memory_write = step;
        }
    }

    // Carry-chained arithmetic leaves a genuine cycle: the new carry is a
    // function of the old accumulator and the new accumulator is a function of
    // the old carry, so neither assignment can go first. On a stack machine
    // that is not a contradiction — push both values, then store both.
    let mut statements: Vec<String> = Vec::new();
    let mut live: Vec<(r2il::Varnode, usize)> = Vec::new();
    let mut live_memory = 0usize;
    let mut scheduled = 0usize;
    for group in schedule(&planned) {
        let rendered = match group.as_slice() {
            [only] => Some(planned[*only].text.clone()),
            members => simultaneous_assignment(&planned, members, &live, live_memory),
        };
        let Some(rendered) = rendered else {
            partial = true;
            continue;
        };
        scheduled += group.len();
        if !rendered.is_empty() {
            statements.push(rendered);
        }
        for position in group {
            if let Some(written) = &planned[position].writes {
                live.push((written.clone(), planned[position].generation));
            }
            if planned[position].writes_memory {
                live_memory = planned[position].generation;
            }
        }
    }
    if scheduled != planned.len() {
        partial = true;
    }

    if partial {
        // `TODO` stops evaluation where it stands, so it can only ever be last.
        statements.push("TODO".to_string());
    }
    statements.join(",")
}

/// Order statements so that each one runs while its operands still hold the
/// generation it was built from.
///
/// Edges are the three classic hazards over the storage each statement touches,
/// plus the same for memory as a single location. Ties break on the original
/// p-code position, so the result is deterministic. Statements that block each
/// other come back as one group to be stored simultaneously.
fn schedule(planned: &[Statement]) -> Vec<Vec<usize>> {
    let count = planned.len();
    let mut edges: Vec<Vec<usize>> = vec![Vec::new(); count];

    for (i, producer) in planned.iter().enumerate() {
        for (j, consumer) in planned.iter().enumerate() {
            if i == j {
                continue;
            }
            let connect = |from: usize, to: usize, edges: &mut Vec<Vec<usize>>| {
                if from != to && !edges[from].contains(&to) {
                    edges[from].push(to);
                }
            };
            if let Some(written) = &producer.writes {
                for (read, generation) in &consumer.needs {
                    if overlaps(written, read) {
                        if *generation == producer.generation {
                            // the consumer wants exactly what this one writes
                            connect(i, j, &mut edges);
                        } else if *generation < producer.generation {
                            // the consumer wants an older value, so it has to
                            // read before this statement overwrites it
                            connect(j, i, &mut edges);
                        }
                    }
                }
                if let Some(other) = &consumer.writes
                    && overlaps(written, other)
                    && producer.generation < consumer.generation
                {
                    connect(i, j, &mut edges);
                }
            }
            if producer.writes_memory {
                if consumer.reads_memory {
                    if consumer.needs_memory == producer.generation {
                        connect(i, j, &mut edges);
                    } else if consumer.needs_memory < producer.generation {
                        connect(j, i, &mut edges);
                    }
                }
                if consumer.writes_memory && producer.generation < consumer.generation {
                    connect(i, j, &mut edges);
                }
            }
        }
    }

    let mut groups: Vec<Vec<usize>> = Vec::new();
    let mut emitted = vec![false; count];
    loop {
        let mut progressed = false;
        loop {
            let ready = (0..count).find(|&i| {
                !emitted[i] && (0..count).all(|j| emitted[j] || j == i || !edges[j].contains(&i))
            });
            let Some(ready) = ready else { break };
            emitted[ready] = true;
            groups.push(vec![ready]);
            progressed = true;
        }
        let Some(seed) = (0..count).find(|&i| !emitted[i]) else {
            return groups;
        };
        // Everything left is blocked. Take the smallest mutually blocked set
        // containing the earliest one, and hand it back as a group; it can only
        // be emitted as a simultaneous assignment, if at all.
        let cycle = mutually_blocked(seed, &edges, &emitted);
        let entered_from_outside = (0..count).any(|j| {
            !emitted[j] && !cycle.contains(&j) && edges[j].iter().any(|to| cycle.contains(to))
        });
        if entered_from_outside && progressed {
            continue;
        }
        if entered_from_outside {
            // A predecessor outside the cycle is itself blocked; nothing more
            // can be ordered.
            groups.push(cycle);
            return groups;
        }
        for &member in &cycle {
            emitted[member] = true;
        }
        groups.push(cycle);
    }
}

/// The statements `seed` is mutually blocked with: it reaches them and they
/// reach it, over the not-yet-emitted part of the graph.
fn mutually_blocked(seed: usize, edges: &[Vec<usize>], emitted: &[bool]) -> Vec<usize> {
    let reach = |from: usize| {
        let mut seen = vec![false; edges.len()];
        let mut stack = vec![from];
        while let Some(node) = stack.pop() {
            for &next in &edges[node] {
                if !emitted[next] && !seen[next] {
                    seen[next] = true;
                    stack.push(next);
                }
            }
        }
        seen
    };
    let forward = reach(seed);
    (0..edges.len())
        .filter(|&node| !emitted[node] && (node == seed || (forward[node] && reach(node)[seed])))
        .collect()
}

/// Where a value has to be stored, as ESIL tokens.
fn assignment_target(disasm: &Disassembler, dst: &r2il::Varnode) -> String {
    match dst.space {
        r2il::SpaceId::Ram => format!("0x{:x},=[{}]", dst.offset, dst.size.clamp(1, 8)),
        _ => format!("{},=", disasm.format_varnode(dst).to_lowercase()),
    }
}

/// Emit a mutually blocked group as one simultaneous assignment.
///
/// Every value is pushed while the operands still hold the generation each was
/// built from, then the stores run in reverse so each pops its own value. Each
/// push is forced through `NUM`, because radare2 keeps a bare register name on
/// the stack unevaluated and would otherwise read it back after the store that
/// changed it. This is only offered when every member is a pure value whose
/// operands are intact at the point the group starts; a member that writes
/// memory keeps its own place and the instruction stays partial instead.
fn simultaneous_assignment(
    planned: &[Statement],
    remaining: &[usize],
    live: &[(r2il::Varnode, usize)],
    live_memory: usize,
) -> Option<String> {
    let mut pushes = Vec::with_capacity(remaining.len());
    let mut stores = Vec::with_capacity(remaining.len());
    for &position in remaining {
        let statement = &planned[position];
        let (expr, store) = statement.split.as_ref()?;
        // Loads are fine, because every value is pushed before any store runs
        // and no store in the group touches memory. A member that writes memory
        // would break that, and so would a load whose memory has moved on.
        if statement.writes_memory {
            return None;
        }
        if statement.reads_memory && statement.needs_memory != live_memory {
            return None;
        }
        let intact = statement.needs.iter().all(|(read, generation)| {
            live.iter()
                .filter(|(written, _)| overlaps(written, read))
                .map(|(_, when)| *when)
                .max()
                .unwrap_or(0)
                == *generation
        });
        if !intact {
            return None;
        }
        pushes.push(format!("{expr},NUM"));
        stores.push(store.clone());
    }
    stores.reverse();
    pushes.extend(stores);
    Some(pushes.join(","))
}

/// One emitted ESIL statement, with what it needs in order to be scheduled.
struct Statement {
    text: String,
    /// For a pure value, the tokens that push it and the tokens that store it,
    /// kept apart so a cycle can be broken by pushing every value first.
    split: Option<(String, String)>,
    /// The generation this statement's own write produces.
    generation: usize,
    /// Each storage read, with the generation of the value it needs.
    needs: Vec<(r2il::Varnode, usize)>,
    reads_memory: bool,
    /// Generation of memory this statement reads, if it reads memory.
    needs_memory: usize,
    writes: Option<r2il::Varnode>,
    writes_memory: bool,
}

/// Whether the operation reads memory on its own account, independent of the
/// expressions spliced into it.
fn reads_memory_directly(op: &R2ILOp) -> bool {
    use r2il::R2ILOp::*;
    matches!(
        op,
        Load { .. } | LoadLinked { .. } | LoadGuarded { .. } | AtomicCAS { .. }
    )
}

/// Whether the operation writes memory, which invalidates any pending value
/// that was read out of memory.
fn writes_memory(op: &R2ILOp) -> bool {
    use r2il::R2ILOp::*;
    matches!(
        op,
        Store { .. }
            | StoreConditional { .. }
            | StoreGuarded { .. }
            | AtomicCAS { .. }
            | Call { .. }
            | CallInd { .. }
            | CallOther { .. }
    )
}

/// Render one operation on its own, for callers that inspect a single p-code
/// step. Whole instructions must go through `block_to_esil`.
pub fn op_to_esil(disasm: &Disassembler, op: &R2ILOp) -> String {
    op_esil(disasm, op).render(disasm)
}

#[cfg(test)]
mod tests {
    use super::{block_to_esil, format_op, op_to_esil};
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
        let dst = Varnode::register(0x00, 4);
        let a = Varnode::register(0x10, 4);
        let b = Varnode::constant(3, 4);
        assert_eq!(
            esil(&R2ILOp::IntSub {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone()
            }),
            "0x3,edx,-,eax,="
        );
        assert_eq!(
            esil(&R2ILOp::IntDiv {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone()
            }),
            "0x3,edx,/,eax,="
        );
        assert_eq!(esil(&R2ILOp::IntSRight { dst, a, b }), "0x3,edx,ASR,eax,=");
    }

    /// `>>>`, `<$`, `<=$`, `~~`, `&&`, `||`, `^^`, `POPCOUNT` and `CLZ` are not
    /// radare2 ESIL operators; emitting them left the expression unevaluated.
    #[test]
    fn only_operators_radare2_defines_are_emitted() {
        const DEFINED: &[&str] = &[
            "+", "-", "*", "/", "%", "~/", "~%", "&", "|", "^", "!", "<<", ">>", "ASR", "ROR",
            "ROL", "~", "==", "=", ":=", "?{", "}", "}{", "$z", "$c", "$b", "$s", "$o", "$p",
            "TODO", "BREAK", "F+", "F-", "F*", "F/", "F==", "F!=", "F<", "F<=", "-F", "SQRT",
            "CEIL", "FLOOR", "ROUND", "I2D", "D2I", "DUP", "SWAP", "NUM",
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
        let dst = Varnode::register(0x200, 1);
        let a = Varnode::register(0x00, 4);
        let b = Varnode::register(0x10, 4);
        assert_eq!(
            esil(&R2ILOp::IntLess {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone()
            }),
            "edx,eax,==,32,$b,cf,="
        );
        assert_eq!(
            esil(&R2ILOp::IntEqual {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone()
            }),
            "edx,eax,==,$z,cf,="
        );
        assert_eq!(
            esil(&R2ILOp::IntSLess {
                dst: dst.clone(),
                a: a.clone(),
                b: b.clone()
            }),
            "edx,eax,==,31,$s,31,$o,0x80000000,edx,-,!,^,^,cf,="
        );
        assert_eq!(
            esil(&R2ILOp::IntSBorrow { dst, a, b }),
            "edx,eax,==,31,$o,0x80000000,edx,-,!,^,cf,="
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
            "0x100000340,rip,="
        );
        assert_eq!(
            esil(&R2ILOp::Call {
                target: Varnode::ram(0x1000004c0, 8)
            }),
            "0x1000004c0,rip,="
        );
    }

    /// The processor spec names the program counter. Writing a branch target to
    /// a register the architecture does not have leaves the branch inert.
    #[test]
    fn the_branch_target_goes_to_the_register_the_spec_names() {
        assert_eq!(x86_64().program_counter(), "RIP");
        let arm = Disassembler::from_sla(
            sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
            sleigh_config::processor_aarch64::PSPEC_AARCH64,
            "aarch64",
        )
        .expect("AArch64 disassembler");
        assert_eq!(arm.program_counter(), "pc");
        assert_eq!(
            op_to_esil(
                &arm,
                &R2ILOp::Branch {
                    target: Varnode::ram(0x1000, 8)
                }
            ),
            "0x1000,pc,="
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
            assert!(esil.ends_with("rip,="), "{op:?} must set the pc: {esil}");
        }
    }

    fn block(ops: Vec<R2ILOp>) -> r2il::R2ILBlock {
        let mut block = r2il::R2ILBlock::new(0x1000, 4);
        block.ops = ops;
        block
    }

    /// radare2 stops evaluating at the first `;`, so joining operations with it
    /// executed the first and silently discarded the rest of the instruction.
    #[test]
    fn instruction_statements_are_joined_with_a_comma() {
        let esil = block_to_esil(
            &x86_64(),
            &block(vec![
                R2ILOp::Copy {
                    dst: Varnode::register(0x00, 8),
                    src: Varnode::constant(0, 8),
                },
                R2ILOp::Copy {
                    dst: Varnode::register(0x08, 8),
                    src: Varnode::constant(0, 8),
                },
            ]),
        );
        assert_eq!(esil, "0x0,rax,=,0x0,rcx,=");
        assert!(!esil.contains(';'));
    }

    /// An ESIL operand is a number or a register; Sleigh's unique space has no
    /// spelling, so a temporary has to be spliced into whoever reads it.
    #[test]
    fn unique_space_temporaries_are_spliced_into_their_reader() {
        let temp = Varnode::unique(0x100, 8);
        let esil = block_to_esil(
            &x86_64(),
            &block(vec![
                R2ILOp::IntAdd {
                    dst: temp.clone(),
                    a: Varnode::register(0x00, 8),
                    b: Varnode::constant(4, 8),
                },
                R2ILOp::Copy {
                    dst: Varnode::register(0x08, 8),
                    src: temp,
                },
            ]),
        );
        assert_eq!(esil, "0x4,rax,+,rcx,=");
        assert!(!esil.contains("tmp:"));
    }

    /// Splicing moves a computation to where its value is read, so the read has
    /// to be scheduled ahead of anything that overwrites what it reads.
    #[test]
    fn a_spliced_read_is_scheduled_before_the_write_that_would_change_it() {
        let temp = Varnode::unique(0x100, 8);
        let esil = block_to_esil(
            &x86_64(),
            &block(vec![
                R2ILOp::IntAdd {
                    dst: temp.clone(),
                    a: Varnode::register(0x00, 8),
                    b: Varnode::constant(4, 8),
                },
                R2ILOp::Copy {
                    dst: Varnode::register(0x00, 8),
                    src: Varnode::constant(9, 8),
                },
                R2ILOp::Copy {
                    dst: Varnode::register(0x08, 8),
                    src: temp,
                },
            ]),
        );
        // rcx must get the sum of the original rax, not of the 9 written after.
        assert_eq!(esil, "0x4,rax,+,rcx,=,0x9,rax,=");
    }

    /// When two statements each need the value the other overwrites, no order
    /// works, but a stack machine can push both values before storing either.
    /// The `NUM` is load bearing: radare2 leaves a bare register name on the
    /// stack unevaluated, so without it the second store reads the value the
    /// first one just wrote.
    #[test]
    fn a_circular_exchange_becomes_a_simultaneous_assignment() {
        let first = Varnode::unique(0x100, 8);
        let second = Varnode::unique(0x108, 8);
        let esil = block_to_esil(
            &x86_64(),
            &block(vec![
                R2ILOp::Copy {
                    dst: first.clone(),
                    src: Varnode::register(0x00, 8),
                },
                R2ILOp::Copy {
                    dst: second.clone(),
                    src: Varnode::register(0x08, 8),
                },
                R2ILOp::Copy {
                    dst: Varnode::register(0x00, 8),
                    src: second,
                },
                R2ILOp::Copy {
                    dst: Varnode::register(0x08, 8),
                    src: first,
                },
            ]),
        );
        assert_eq!(esil, "rcx,NUM,rax,NUM,rcx,=,rax,=");
    }

    /// One unmodelled operation must not cost the whole instruction. The
    /// register write still lands even though the float operation does not.
    #[test]
    fn an_unmodelled_operation_only_drops_what_depends_on_it() {
        let temp = Varnode::unique(0x100, 8);
        let esil = block_to_esil(
            &x86_64(),
            &block(vec![
                R2ILOp::Copy {
                    dst: Varnode::register(0x00, 8),
                    src: Varnode::constant(0, 8),
                },
                R2ILOp::FloatAbs {
                    dst: temp.clone(),
                    src: Varnode::register(0x08, 8),
                },
                R2ILOp::Copy {
                    dst: Varnode::register(0x10, 8),
                    src: temp,
                },
            ]),
        );
        assert_eq!(esil, "0x0,rax,=,TODO");
    }

    /// The shape every x86 shift and compare has: save an operand, overwrite
    /// the register, then derive a flag from what was saved. Once the saved
    /// value is spliced back in, the flag has to be emitted ahead of the write.
    #[test]
    fn a_flag_built_from_a_saved_operand_is_emitted_before_the_write() {
        let saved = Varnode::unique(0x100, 8);
        let esil = block_to_esil(
            &x86_64(),
            &block(vec![
                // saved = rax
                R2ILOp::Copy {
                    dst: saved.clone(),
                    src: Varnode::register(0x00, 8),
                },
                // rax = rax + 1
                R2ILOp::IntAdd {
                    dst: Varnode::register(0x00, 8),
                    a: Varnode::register(0x00, 8),
                    b: Varnode::constant(1, 8),
                },
                // cf = saved, i.e. the value rax held before the add
                R2ILOp::Copy {
                    dst: Varnode::register(0x200, 1),
                    src: saved,
                },
            ]),
        );
        assert_eq!(esil, "rax,cf,=,0x1,rax,+,rax,=");
        assert!(!esil.contains("TODO"));
    }

    /// radare2 defines no popcount, but `DUP` and `SWAP` are enough to write
    /// the SWAR reduction out, which is what x86 parity needs.
    #[test]
    fn population_count_is_computed_rather_than_refused() {
        let esil = esil(&R2ILOp::PopCount {
            dst: Varnode::register(0x00, 8),
            src: Varnode::register(0x08, 8),
        });
        assert!(esil.starts_with("0xffffffffffffffff,rcx,&,DUP,"), "{esil}");
        assert!(esil.ends_with("56,SWAP,>>,rax,="), "{esil}");
        assert!(!esil.contains("TODO"));
    }

    /// `TODO` stops radare2's evaluator where it stands, so a partial
    /// instruction must carry it last or it would truncate the rest.
    #[test]
    fn the_partial_marker_never_precedes_a_statement() {
        let esil = block_to_esil(
            &x86_64(),
            &block(vec![
                R2ILOp::FloatNaN {
                    dst: Varnode::unique(0x100, 1),
                    src: Varnode::register(0x00, 8),
                },
                R2ILOp::Copy {
                    dst: Varnode::register(0x08, 8),
                    src: Varnode::constant(7, 8),
                },
            ]),
        );
        assert_eq!(esil, "0x7,rcx,=,TODO");
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
