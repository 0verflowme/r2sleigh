//! SSA operation definitions.
//!
//! These mirror r2il::R2ILOp but use SSAVar instead of Varnode,
//! providing versioned variables for dataflow analysis.

use serde::{Deserialize, Serialize};

use crate::var::SSAVar;
use r2il::MemoryOrdering;

/// An SSA operation representing a single semantic action with versioned variables.
///
/// Each operation uses SSAVar which includes version numbers, enabling
/// precise tracking of definitions and uses for dataflow analysis.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum SSAOp {
    // ========== SSA-specific Operations ==========
    /// Phi function: merges values from different control flow paths.
    /// dst = phi(sources[0], sources[1], ...)
    Phi { dst: SSAVar, sources: Vec<SSAVar> },

    // ========== Data Movement ==========
    /// Copy src to dst: dst = src
    Copy { dst: SSAVar, src: SSAVar },

    /// Load from memory: dst = *[space]addr
    Load {
        dst: SSAVar,
        space: String,
        addr: SSAVar,
    },

    /// Store to memory: *[space]addr = val
    Store {
        space: String,
        addr: SSAVar,
        val: SSAVar,
    },

    /// Memory fence/barrier.
    Fence { ordering: MemoryOrdering },

    /// Load-linked from memory.
    LoadLinked {
        dst: SSAVar,
        space: String,
        addr: SSAVar,
        ordering: MemoryOrdering,
    },

    /// Store-conditional to memory.
    StoreConditional {
        result: Option<SSAVar>,
        space: String,
        addr: SSAVar,
        val: SSAVar,
        ordering: MemoryOrdering,
    },

    /// Atomic compare-and-swap.
    AtomicCAS {
        dst: SSAVar,
        space: String,
        addr: SSAVar,
        expected: SSAVar,
        replacement: SSAVar,
        ordering: MemoryOrdering,
    },

    /// Guarded memory load.
    LoadGuarded {
        dst: SSAVar,
        space: String,
        addr: SSAVar,
        guard: SSAVar,
        ordering: MemoryOrdering,
    },

    /// Guarded memory store.
    StoreGuarded {
        space: String,
        addr: SSAVar,
        val: SSAVar,
        guard: SSAVar,
        ordering: MemoryOrdering,
    },

    // ========== Integer Arithmetic ==========
    /// Integer addition: dst = a + b
    IntAdd { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Integer subtraction: dst = a - b
    IntSub { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Integer multiplication: dst = a * b
    IntMult { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Unsigned integer division: dst = a / b
    IntDiv { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Signed integer division: dst = a / b (signed)
    IntSDiv { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Unsigned integer remainder: dst = a % b
    IntRem { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Signed integer remainder: dst = a % b (signed)
    IntSRem { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Two's complement negation: dst = -src
    IntNegate { dst: SSAVar, src: SSAVar },

    /// Addition with carry: dst = a + b + carry
    IntCarry { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Signed carry (overflow): dst = overflow(a + b)
    IntSCarry { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Signed borrow: dst = borrow(a - b)
    IntSBorrow { dst: SSAVar, a: SSAVar, b: SSAVar },

    // ========== Logical Operations ==========
    /// Bitwise AND: dst = a & b
    IntAnd { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Bitwise OR: dst = a | b
    IntOr { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Bitwise XOR: dst = a ^ b
    IntXor { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Bitwise NOT: dst = ~src
    IntNot { dst: SSAVar, src: SSAVar },

    // ========== Shift Operations ==========
    /// Left shift: dst = a << b
    IntLeft { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Logical right shift: dst = a >> b (unsigned)
    IntRight { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Arithmetic right shift: dst = a >> b (signed)
    IntSRight { dst: SSAVar, a: SSAVar, b: SSAVar },

    // ========== Comparison Operations ==========
    /// Equality: dst = (a == b) ? 1 : 0
    IntEqual { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Inequality: dst = (a != b) ? 1 : 0
    IntNotEqual { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Unsigned less than: dst = (a < b) ? 1 : 0
    IntLess { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Signed less than: dst = (a < b) ? 1 : 0 (signed)
    IntSLess { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Unsigned less or equal: dst = (a <= b) ? 1 : 0
    IntLessEqual { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Signed less or equal: dst = (a <= b) ? 1 : 0 (signed)
    IntSLessEqual { dst: SSAVar, a: SSAVar, b: SSAVar },

    // ========== Extension Operations ==========
    /// Zero extension: dst = zext(src)
    IntZExt { dst: SSAVar, src: SSAVar },

    /// Sign extension: dst = sext(src)
    IntSExt { dst: SSAVar, src: SSAVar },

    // ========== Boolean Operations ==========
    /// Boolean NOT: dst = !src
    BoolNot { dst: SSAVar, src: SSAVar },

    /// Boolean AND: dst = a && b
    BoolAnd { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Boolean OR: dst = a || b
    BoolOr { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Boolean XOR: dst = a ^^ b
    BoolXor { dst: SSAVar, a: SSAVar, b: SSAVar },

    // ========== Bit Manipulation ==========
    /// Concatenate two values: dst = (hi << lo.size*8) | lo
    Piece { dst: SSAVar, hi: SSAVar, lo: SSAVar },

    /// Extract a portion of a value: dst = src[offset:size]
    Subpiece {
        dst: SSAVar,
        src: SSAVar,
        offset: u32,
    },

    /// Population count (number of 1 bits): dst = popcount(src)
    PopCount { dst: SSAVar, src: SSAVar },

    /// Count leading zeros: dst = clz(src)
    Lzcount { dst: SSAVar, src: SSAVar },

    // ========== Control Flow ==========
    /// Unconditional branch to target
    Branch { target: SSAVar },

    /// Conditional branch: if (cond) goto target
    CBranch { target: SSAVar, cond: SSAVar },

    /// Indirect branch: goto *target
    BranchInd { target: SSAVar },

    /// Call a subroutine
    Call { target: SSAVar },

    /// Indirect call: call *target
    CallInd { target: SSAVar },

    /// Fresh unknown register value defined by a call boundary.
    ///
    /// Decompiler-safe SSA emits this after calls for return/caller-saved
    /// registers so later reads cannot reuse pre-call versions.
    CallDefine { dst: SSAVar },

    /// Return from subroutine
    Return { target: SSAVar },

    // ========== Floating Point ==========
    /// Float addition: dst = a + b
    FloatAdd { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Float subtraction: dst = a - b
    FloatSub { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Float multiplication: dst = a * b
    FloatMult { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Float division: dst = a / b
    FloatDiv { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Float negation: dst = -src
    FloatNeg { dst: SSAVar, src: SSAVar },

    /// Float absolute value: dst = |src|
    FloatAbs { dst: SSAVar, src: SSAVar },

    /// Float square root: dst = sqrt(src)
    FloatSqrt { dst: SSAVar, src: SSAVar },

    /// Float ceiling: dst = ceil(src)
    FloatCeil { dst: SSAVar, src: SSAVar },

    /// Float floor: dst = floor(src)
    FloatFloor { dst: SSAVar, src: SSAVar },

    /// Float round: dst = round(src)
    FloatRound { dst: SSAVar, src: SSAVar },

    /// Float is NaN: dst = isnan(src)
    FloatNaN { dst: SSAVar, src: SSAVar },

    /// Float equality: dst = (a == b) ? 1 : 0
    FloatEqual { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Float not equal: dst = (a != b) ? 1 : 0
    FloatNotEqual { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Float less than: dst = (a < b) ? 1 : 0
    FloatLess { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Float less or equal: dst = (a <= b) ? 1 : 0
    FloatLessEqual { dst: SSAVar, a: SSAVar, b: SSAVar },

    /// Convert int to float: dst = (float)src
    Int2Float { dst: SSAVar, src: SSAVar },

    /// Convert float to int: dst = (int)src
    Float2Int { dst: SSAVar, src: SSAVar },

    /// Convert float to different size float: dst = (float_new_size)src
    FloatFloat { dst: SSAVar, src: SSAVar },

    /// Truncate float to int: dst = trunc(src)
    Trunc { dst: SSAVar, src: SSAVar },

    // ========== Special Operations ==========
    /// Call a user-defined operation (CALLOTHER in P-code)
    CallOther {
        /// Optional output varnode
        output: Option<SSAVar>,
        /// User-defined operation index
        userop: u32,
        /// Input arguments
        inputs: Vec<SSAVar>,
    },

    /// No operation (placeholder)
    Nop,

    /// Unimplemented instruction
    Unimplemented,

    /// CPU identification (CPUID-like)
    CpuId { dst: SSAVar },

    /// Insert a breakpoint
    Breakpoint,

    /// Pointer addition: dst = base + (index * element_size)
    PtrAdd {
        dst: SSAVar,
        base: SSAVar,
        index: SSAVar,
        element_size: u32,
    },

    /// Pointer subtraction: dst = base - (index * element_size)
    PtrSub {
        dst: SSAVar,
        base: SSAVar,
        index: SSAVar,
        element_size: u32,
    },

    /// Segment calculation: dst = segment:offset
    SegmentOp {
        dst: SSAVar,
        segment: SSAVar,
        offset: SSAVar,
    },

    /// New (allocation, used in high-level analysis)
    New { dst: SSAVar, src: SSAVar },

    /// Cast (type cast, used in high-level analysis)
    Cast { dst: SSAVar, src: SSAVar },

    /// Extract (bit field extraction)
    Extract {
        dst: SSAVar,
        src: SSAVar,
        position: SSAVar,
    },

    /// Insert (bit field insertion)
    Insert {
        dst: SSAVar,
        src: SSAVar,
        value: SSAVar,
        position: SSAVar,
    },
}

impl SSAOp {
    /// Get the destination variable if this operation has one.
    pub fn dst(&self) -> Option<&SSAVar> {
        use SSAOp::*;
        match self {
            Phi { dst, .. }
            | Copy { dst, .. }
            | Load { dst, .. }
            | LoadLinked { dst, .. }
            | AtomicCAS { dst, .. }
            | LoadGuarded { dst, .. }
            | IntAdd { dst, .. }
            | IntSub { dst, .. }
            | IntMult { dst, .. }
            | IntDiv { dst, .. }
            | IntSDiv { dst, .. }
            | IntRem { dst, .. }
            | IntSRem { dst, .. }
            | IntNegate { dst, .. }
            | IntCarry { dst, .. }
            | IntSCarry { dst, .. }
            | IntSBorrow { dst, .. }
            | IntAnd { dst, .. }
            | IntOr { dst, .. }
            | IntXor { dst, .. }
            | IntNot { dst, .. }
            | IntLeft { dst, .. }
            | IntRight { dst, .. }
            | IntSRight { dst, .. }
            | IntEqual { dst, .. }
            | IntNotEqual { dst, .. }
            | IntLess { dst, .. }
            | IntSLess { dst, .. }
            | IntLessEqual { dst, .. }
            | IntSLessEqual { dst, .. }
            | IntZExt { dst, .. }
            | IntSExt { dst, .. }
            | BoolNot { dst, .. }
            | BoolAnd { dst, .. }
            | BoolOr { dst, .. }
            | BoolXor { dst, .. }
            | Piece { dst, .. }
            | Subpiece { dst, .. }
            | PopCount { dst, .. }
            | Lzcount { dst, .. }
            | FloatAdd { dst, .. }
            | FloatSub { dst, .. }
            | FloatMult { dst, .. }
            | FloatDiv { dst, .. }
            | FloatNeg { dst, .. }
            | FloatAbs { dst, .. }
            | FloatSqrt { dst, .. }
            | FloatCeil { dst, .. }
            | FloatFloor { dst, .. }
            | FloatRound { dst, .. }
            | FloatNaN { dst, .. }
            | FloatEqual { dst, .. }
            | FloatNotEqual { dst, .. }
            | FloatLess { dst, .. }
            | FloatLessEqual { dst, .. }
            | Int2Float { dst, .. }
            | Float2Int { dst, .. }
            | FloatFloat { dst, .. }
            | Trunc { dst, .. }
            | CpuId { dst, .. }
            | PtrAdd { dst, .. }
            | PtrSub { dst, .. }
            | SegmentOp { dst, .. }
            | New { dst, .. }
            | Cast { dst, .. }
            | Extract { dst, .. }
            | Insert { dst, .. }
            | CallDefine { dst } => Some(dst),

            CallOther { output, .. } | StoreConditional { result: output, .. } => output.as_ref(),

            Store { .. }
            | Fence { .. }
            | StoreGuarded { .. }
            | Branch { .. }
            | CBranch { .. }
            | BranchInd { .. }
            | Call { .. }
            | CallInd { .. }
            | Return { .. }
            | Nop
            | Unimplemented
            | Breakpoint => None,
        }
    }

    /// Visit all source variables used by this operation in operand order.
    pub fn for_each_source<'a, F: FnMut(&'a SSAVar)>(&'a self, mut f: F) {
        use SSAOp::*;
        match self {
            Phi { sources, .. } => {
                for src in sources {
                    f(src);
                }
            }

            Copy { src, .. }
            | IntNegate { src, .. }
            | IntNot { src, .. }
            | IntZExt { src, .. }
            | IntSExt { src, .. }
            | BoolNot { src, .. }
            | Subpiece { src, .. }
            | PopCount { src, .. }
            | Lzcount { src, .. }
            | FloatNeg { src, .. }
            | FloatAbs { src, .. }
            | FloatSqrt { src, .. }
            | FloatCeil { src, .. }
            | FloatFloor { src, .. }
            | FloatRound { src, .. }
            | FloatNaN { src, .. }
            | Int2Float { src, .. }
            | Float2Int { src, .. }
            | FloatFloat { src, .. }
            | Trunc { src, .. }
            | New { src, .. }
            | Cast { src, .. } => f(src),

            Load { addr, .. } | LoadLinked { addr, .. } => f(addr),

            Store { addr, val, .. } | StoreConditional { addr, val, .. } => {
                f(addr);
                f(val);
            }

            AtomicCAS {
                addr,
                expected,
                replacement,
                ..
            } => {
                f(addr);
                f(expected);
                f(replacement);
            }

            LoadGuarded { addr, guard, .. } => {
                f(addr);
                f(guard);
            }

            StoreGuarded {
                addr, val, guard, ..
            } => {
                f(addr);
                f(val);
                f(guard);
            }

            IntAdd { a, b, .. }
            | IntSub { a, b, .. }
            | IntMult { a, b, .. }
            | IntDiv { a, b, .. }
            | IntSDiv { a, b, .. }
            | IntRem { a, b, .. }
            | IntSRem { a, b, .. }
            | IntCarry { a, b, .. }
            | IntSCarry { a, b, .. }
            | IntSBorrow { a, b, .. }
            | IntAnd { a, b, .. }
            | IntOr { a, b, .. }
            | IntXor { a, b, .. }
            | IntLeft { a, b, .. }
            | IntRight { a, b, .. }
            | IntSRight { a, b, .. }
            | IntEqual { a, b, .. }
            | IntNotEqual { a, b, .. }
            | IntLess { a, b, .. }
            | IntSLess { a, b, .. }
            | IntLessEqual { a, b, .. }
            | IntSLessEqual { a, b, .. }
            | BoolAnd { a, b, .. }
            | BoolOr { a, b, .. }
            | BoolXor { a, b, .. }
            | FloatAdd { a, b, .. }
            | FloatSub { a, b, .. }
            | FloatMult { a, b, .. }
            | FloatDiv { a, b, .. }
            | FloatEqual { a, b, .. }
            | FloatNotEqual { a, b, .. }
            | FloatLess { a, b, .. }
            | FloatLessEqual { a, b, .. } => {
                f(a);
                f(b);
            }

            Piece { hi, lo, .. } => {
                f(hi);
                f(lo);
            }

            Extract { src, position, .. } => {
                f(src);
                f(position);
            }

            Insert {
                src,
                value,
                position,
                ..
            } => {
                f(src);
                f(value);
                f(position);
            }

            PtrAdd { base, index, .. } | PtrSub { base, index, .. } => {
                f(base);
                f(index);
            }

            SegmentOp {
                segment, offset, ..
            } => {
                f(segment);
                f(offset);
            }

            Branch { target }
            | BranchInd { target }
            | Call { target }
            | CallInd { target }
            | Return { target } => f(target),

            CBranch { target, cond } => {
                f(target);
                f(cond);
            }

            CallOther { inputs, .. } => {
                for input in inputs {
                    f(input);
                }
            }

            Fence { .. } | Nop | Unimplemented | Breakpoint | CpuId { .. } | CallDefine { .. } => {}
        }
    }

    /// Get all source variables used by this operation.
    pub fn sources(&self) -> Vec<&SSAVar> {
        let mut sources = Vec::new();
        self.for_each_source(|src| sources.push(src));
        sources
    }

    /// Returns true if this operation is a control flow operation.
    pub fn is_control_flow(&self) -> bool {
        matches!(
            self,
            SSAOp::Branch { .. }
                | SSAOp::CBranch { .. }
                | SSAOp::BranchInd { .. }
                | SSAOp::Call { .. }
                | SSAOp::CallInd { .. }
                | SSAOp::Return { .. }
        )
    }

    /// Returns true if this operation reads from memory.
    pub fn is_memory_read(&self) -> bool {
        matches!(
            self,
            SSAOp::Load { .. }
                | SSAOp::LoadLinked { .. }
                | SSAOp::LoadGuarded { .. }
                | SSAOp::AtomicCAS { .. }
        )
    }

    /// Returns true if this operation writes to memory.
    pub fn is_memory_write(&self) -> bool {
        matches!(
            self,
            SSAOp::Store { .. }
                | SSAOp::StoreConditional { .. }
                | SSAOp::StoreGuarded { .. }
                | SSAOp::AtomicCAS { .. }
        )
    }

    /// Returns true if this is a phi node.
    pub fn is_phi(&self) -> bool {
        matches!(self, SSAOp::Phi { .. })
    }
}

impl std::fmt::Display for SSAOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SSAOp::Phi { dst, sources } => {
                write!(f, "{} = PHI(", dst)?;
                for (i, src) in sources.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", src)?;
                }
                write!(f, ")")
            }
            SSAOp::Copy { dst, src } => write!(f, "{} = COPY {}", dst, src),
            SSAOp::Load { dst, space, addr } => write!(f, "{} = LOAD [{}]{}", dst, space, addr),
            SSAOp::Store { space, addr, val } => write!(f, "STORE [{}]{} = {}", space, addr, val),
            SSAOp::Fence { ordering } => write!(f, "FENCE({:?})", ordering),
            SSAOp::LoadLinked {
                dst,
                space,
                addr,
                ordering,
            } => write!(
                f,
                "{} = LOAD_LINKED({:?}) [{}]{}",
                dst, ordering, space, addr
            ),
            SSAOp::StoreConditional {
                result,
                space,
                addr,
                val,
                ordering,
            } => {
                if let Some(out) = result {
                    write!(f, "{} = ", out)?;
                }
                write!(
                    f,
                    "STORE_CONDITIONAL({:?}) [{}]{} = {}",
                    ordering, space, addr, val
                )
            }
            SSAOp::AtomicCAS {
                dst,
                space,
                addr,
                expected,
                replacement,
                ordering,
            } => write!(
                f,
                "{} = ATOMIC_CAS({:?}) [{}]{}, {}, {}",
                dst, ordering, space, addr, expected, replacement
            ),
            SSAOp::LoadGuarded {
                dst,
                space,
                addr,
                guard,
                ordering,
            } => write!(
                f,
                "{} = LOAD_GUARDED({:?}) [{}]{}, guard={}",
                dst, ordering, space, addr, guard
            ),
            SSAOp::StoreGuarded {
                space,
                addr,
                val,
                guard,
                ordering,
            } => write!(
                f,
                "STORE_GUARDED({:?}) [{}]{} = {}, guard={}",
                ordering, space, addr, val, guard
            ),
            SSAOp::IntAdd { dst, a, b } => write!(f, "{} = {} + {}", dst, a, b),
            SSAOp::IntSub { dst, a, b } => write!(f, "{} = {} - {}", dst, a, b),
            SSAOp::IntMult { dst, a, b } => write!(f, "{} = {} * {}", dst, a, b),
            SSAOp::IntDiv { dst, a, b } => write!(f, "{} = {} / {}", dst, a, b),
            SSAOp::IntSDiv { dst, a, b } => write!(f, "{} = {} s/ {}", dst, a, b),
            SSAOp::IntRem { dst, a, b } => write!(f, "{} = {} % {}", dst, a, b),
            SSAOp::IntSRem { dst, a, b } => write!(f, "{} = {} s% {}", dst, a, b),
            SSAOp::IntNegate { dst, src } => write!(f, "{} = -{}", dst, src),
            SSAOp::IntCarry { dst, a, b } => write!(f, "{} = CARRY({}, {})", dst, a, b),
            SSAOp::IntSCarry { dst, a, b } => write!(f, "{} = SCARRY({}, {})", dst, a, b),
            SSAOp::IntSBorrow { dst, a, b } => write!(f, "{} = SBORROW({}, {})", dst, a, b),
            SSAOp::IntAnd { dst, a, b } => write!(f, "{} = {} & {}", dst, a, b),
            SSAOp::IntOr { dst, a, b } => write!(f, "{} = {} | {}", dst, a, b),
            SSAOp::IntXor { dst, a, b } => write!(f, "{} = {} ^ {}", dst, a, b),
            SSAOp::IntNot { dst, src } => write!(f, "{} = ~{}", dst, src),
            SSAOp::IntLeft { dst, a, b } => write!(f, "{} = {} << {}", dst, a, b),
            SSAOp::IntRight { dst, a, b } => write!(f, "{} = {} >> {}", dst, a, b),
            SSAOp::IntSRight { dst, a, b } => write!(f, "{} = {} s>> {}", dst, a, b),
            SSAOp::IntEqual { dst, a, b } => write!(f, "{} = {} == {}", dst, a, b),
            SSAOp::IntNotEqual { dst, a, b } => write!(f, "{} = {} != {}", dst, a, b),
            SSAOp::IntLess { dst, a, b } => write!(f, "{} = {} < {}", dst, a, b),
            SSAOp::IntSLess { dst, a, b } => write!(f, "{} = {} s< {}", dst, a, b),
            SSAOp::IntLessEqual { dst, a, b } => write!(f, "{} = {} <= {}", dst, a, b),
            SSAOp::IntSLessEqual { dst, a, b } => write!(f, "{} = {} s<= {}", dst, a, b),
            SSAOp::IntZExt { dst, src } => write!(f, "{} = ZEXT({})", dst, src),
            SSAOp::IntSExt { dst, src } => write!(f, "{} = SEXT({})", dst, src),
            SSAOp::BoolNot { dst, src } => write!(f, "{} = !{}", dst, src),
            SSAOp::BoolAnd { dst, a, b } => write!(f, "{} = {} && {}", dst, a, b),
            SSAOp::BoolOr { dst, a, b } => write!(f, "{} = {} || {}", dst, a, b),
            SSAOp::BoolXor { dst, a, b } => write!(f, "{} = {} ^^ {}", dst, a, b),
            SSAOp::Piece { dst, hi, lo } => write!(f, "{} = PIECE({}, {})", dst, hi, lo),
            SSAOp::Subpiece { dst, src, offset } => {
                write!(f, "{} = SUBPIECE({}, {})", dst, src, offset)
            }
            SSAOp::PopCount { dst, src } => write!(f, "{} = POPCOUNT({})", dst, src),
            SSAOp::Lzcount { dst, src } => write!(f, "{} = LZCOUNT({})", dst, src),
            SSAOp::Branch { target } => write!(f, "BRANCH {}", target),
            SSAOp::CBranch { target, cond } => write!(f, "CBRANCH {} if {}", target, cond),
            SSAOp::BranchInd { target } => write!(f, "BRANCHIND {}", target),
            SSAOp::Call { target } => write!(f, "CALL {}", target),
            SSAOp::CallInd { target } => write!(f, "CALLIND {}", target),
            SSAOp::CallDefine { dst } => write!(f, "{} = CALLDEF", dst),
            SSAOp::Return { target } => write!(f, "RETURN {}", target),
            SSAOp::FloatAdd { dst, a, b } => write!(f, "{} = {} f+ {}", dst, a, b),
            SSAOp::FloatSub { dst, a, b } => write!(f, "{} = {} f- {}", dst, a, b),
            SSAOp::FloatMult { dst, a, b } => write!(f, "{} = {} f* {}", dst, a, b),
            SSAOp::FloatDiv { dst, a, b } => write!(f, "{} = {} f/ {}", dst, a, b),
            SSAOp::FloatNeg { dst, src } => write!(f, "{} = f-{}", dst, src),
            SSAOp::FloatAbs { dst, src } => write!(f, "{} = FABS({})", dst, src),
            SSAOp::FloatSqrt { dst, src } => write!(f, "{} = FSQRT({})", dst, src),
            SSAOp::FloatCeil { dst, src } => write!(f, "{} = FCEIL({})", dst, src),
            SSAOp::FloatFloor { dst, src } => write!(f, "{} = FFLOOR({})", dst, src),
            SSAOp::FloatRound { dst, src } => write!(f, "{} = FROUND({})", dst, src),
            SSAOp::FloatNaN { dst, src } => write!(f, "{} = FNAN({})", dst, src),
            SSAOp::FloatEqual { dst, a, b } => write!(f, "{} = {} f== {}", dst, a, b),
            SSAOp::FloatNotEqual { dst, a, b } => write!(f, "{} = {} f!= {}", dst, a, b),
            SSAOp::FloatLess { dst, a, b } => write!(f, "{} = {} f< {}", dst, a, b),
            SSAOp::FloatLessEqual { dst, a, b } => write!(f, "{} = {} f<= {}", dst, a, b),
            SSAOp::Int2Float { dst, src } => write!(f, "{} = INT2FLOAT({})", dst, src),
            SSAOp::Float2Int { dst, src } => write!(f, "{} = FLOAT2INT({})", dst, src),
            SSAOp::FloatFloat { dst, src } => write!(f, "{} = FLOAT2FLOAT({})", dst, src),
            SSAOp::Trunc { dst, src } => write!(f, "{} = TRUNC({})", dst, src),
            SSAOp::CallOther {
                output,
                userop,
                inputs,
            } => {
                if let Some(out) = output {
                    write!(f, "{} = ", out)?;
                }
                write!(f, "CALLOTHER({})", userop)?;
                if !inputs.is_empty() {
                    write!(f, " [")?;
                    for (i, inp) in inputs.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", inp)?;
                    }
                    write!(f, "]")?;
                }
                Ok(())
            }
            SSAOp::Nop => write!(f, "NOP"),
            SSAOp::Unimplemented => write!(f, "UNIMPLEMENTED"),
            SSAOp::CpuId { dst } => write!(f, "{} = CPUID", dst),
            SSAOp::Breakpoint => write!(f, "BREAKPOINT"),
            SSAOp::PtrAdd {
                dst,
                base,
                index,
                element_size,
            } => write!(f, "{} = PTRADD({}, {}, {})", dst, base, index, element_size),
            SSAOp::PtrSub {
                dst,
                base,
                index,
                element_size,
            } => write!(f, "{} = PTRSUB({}, {}, {})", dst, base, index, element_size),
            SSAOp::SegmentOp {
                dst,
                segment,
                offset,
            } => write!(f, "{} = SEGMENT({}, {})", dst, segment, offset),
            SSAOp::New { dst, src } => write!(f, "{} = NEW({})", dst, src),
            SSAOp::Cast { dst, src } => write!(f, "{} = CAST({})", dst, src),
            SSAOp::Extract { dst, src, position } => {
                write!(f, "{} = EXTRACT({}, {})", dst, src, position)
            }
            SSAOp::Insert {
                dst,
                src,
                value,
                position,
            } => write!(f, "{} = INSERT({}, {}, {})", dst, src, value, position),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dst_extraction() {
        let dst = SSAVar::new("RAX", 1, 8);
        let src = SSAVar::new("RBX", 0, 8);

        let op = SSAOp::Copy {
            dst: dst.clone(),
            src,
        };
        assert_eq!(op.dst(), Some(&dst));

        let op = SSAOp::Nop;
        assert_eq!(op.dst(), None);
    }

    #[test]
    fn test_sources_extraction() {
        let a = SSAVar::new("RAX", 0, 8);
        let b = SSAVar::new("RBX", 0, 8);
        let dst = SSAVar::new("RCX", 1, 8);

        let op = SSAOp::IntAdd {
            dst,
            a: a.clone(),
            b: b.clone(),
        };
        let sources = op.sources();
        assert_eq!(sources.len(), 2);
        assert_eq!(sources[0], &a);
        assert_eq!(sources[1], &b);
    }

    #[test]
    fn test_phi_sources() {
        let dst = SSAVar::new("RAX", 2, 8);
        let s1 = SSAVar::new("RAX", 0, 8);
        let s2 = SSAVar::new("RAX", 1, 8);

        let op = SSAOp::Phi {
            dst,
            sources: vec![s1.clone(), s2.clone()],
        };
        let sources = op.sources();
        assert_eq!(sources.len(), 2);
        assert_eq!(sources[0], &s1);
        assert_eq!(sources[1], &s2);
    }

    #[test]
    fn test_display() {
        let op = SSAOp::Copy {
            dst: SSAVar::new("RAX", 1, 8),
            src: SSAVar::new("RAX", 0, 8),
        };
        assert_eq!(format!("{}", op), "RAX_1 = COPY RAX_0");
    }

    #[test]
    fn test_display_phi() {
        let op = SSAOp::Phi {
            dst: SSAVar::new("RAX", 2, 8),
            sources: vec![SSAVar::new("RAX", 0, 8), SSAVar::new("RAX", 1, 8)],
        };
        assert_eq!(format!("{}", op), "RAX_2 = PHI(RAX_0, RAX_1)");
    }

    #[test]
    fn test_display_load_store() {
        let load = SSAOp::Load {
            dst: SSAVar::new("RAX", 1, 8),
            space: "ram".to_string(),
            addr: SSAVar::new("RSP", 0, 8),
        };
        assert_eq!(format!("{}", load), "RAX_1 = LOAD [ram]RSP_0");

        let store = SSAOp::Store {
            space: "ram".to_string(),
            addr: SSAVar::new("RSP", 0, 8),
            val: SSAVar::new("RAX", 1, 8),
        };
        assert_eq!(format!("{}", store), "STORE [ram]RSP_0 = RAX_1");
    }

    #[test]
    fn test_for_each_source_matches_sources() {
        let ops = vec![
            SSAOp::Phi {
                dst: SSAVar::new("RAX", 2, 8),
                sources: vec![SSAVar::new("RAX", 0, 8), SSAVar::new("RAX", 1, 8)],
            },
            SSAOp::IntAdd {
                dst: SSAVar::new("RCX", 1, 8),
                a: SSAVar::new("RAX", 1, 8),
                b: SSAVar::new("RBX", 0, 8),
            },
            SSAOp::Store {
                space: "ram".to_string(),
                addr: SSAVar::new("RSP", 0, 8),
                val: SSAVar::new("RAX", 1, 8),
            },
            SSAOp::CallOther {
                output: None,
                userop: 1,
                inputs: vec![SSAVar::new("RDI", 0, 8), SSAVar::new("RSI", 0, 8)],
            },
        ];

        for op in &ops {
            let from_sources: Vec<String> = op.sources().iter().map(|v| v.display_name()).collect();
            let mut from_visitor = Vec::new();
            op.for_each_source(|v| from_visitor.push(v.display_name()));
            assert_eq!(
                from_sources, from_visitor,
                "for_each_source must preserve order and membership for {:?}",
                op
            );
        }
    }
}
