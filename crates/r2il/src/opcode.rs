//! r2il opcode definitions.
//!
//! These opcodes are based on Ghidra's P-code operations, providing a strongly-typed
//! intermediate representation for processor instruction semantics.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

use crate::memory::MemoryOrdering;
use crate::metadata::OpMetadata;
use crate::space::SpaceId;
use crate::varnode::Varnode;

/// An r2il operation representing a single semantic action.
///
/// Operations are organized into categories:
/// - Data movement (Copy, Load, Store)
/// - Integer arithmetic (Add, Sub, Mult, Div, etc.)
/// - Logical operations (And, Or, Xor, Not)
/// - Comparison operations (Equal, NotEqual, Less, etc.)
/// - Bit manipulation (Shift, Rotate, etc.)
/// - Control flow (Branch, CBranch, Call, Return)
/// - Floating point (FloatAdd, FloatSub, etc.)
/// - Special operations (Piece, Subpiece, etc.)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum R2ILOp {
    // ========== Data Movement ==========
    /// Copy src to dst: dst = src
    Copy { dst: Varnode, src: Varnode },

    /// Load from memory: dst = *[space]addr
    Load {
        dst: Varnode,
        space: SpaceId,
        addr: Varnode,
    },

    /// Store to memory: *[space]addr = val
    Store {
        space: SpaceId,
        addr: Varnode,
        val: Varnode,
    },

    /// Memory fence/barrier with ordering semantics.
    Fence { ordering: MemoryOrdering },

    /// Linked load from memory: dst = LL(*[space]addr).
    LoadLinked {
        dst: Varnode,
        space: SpaceId,
        addr: Varnode,
        ordering: MemoryOrdering,
    },

    /// Conditional store to memory; optional result receives success status.
    StoreConditional {
        result: Option<Varnode>,
        space: SpaceId,
        addr: Varnode,
        val: Varnode,
        ordering: MemoryOrdering,
    },

    /// Atomic compare and exchange: dst = CAS(*addr, expected, replacement).
    AtomicCAS {
        dst: Varnode,
        space: SpaceId,
        addr: Varnode,
        expected: Varnode,
        replacement: Varnode,
        ordering: MemoryOrdering,
    },

    /// Guarded load from memory: if guard then load.
    LoadGuarded {
        dst: Varnode,
        space: SpaceId,
        addr: Varnode,
        guard: Varnode,
        ordering: MemoryOrdering,
    },

    /// Guarded store to memory: if guard then store.
    StoreGuarded {
        space: SpaceId,
        addr: Varnode,
        val: Varnode,
        guard: Varnode,
        ordering: MemoryOrdering,
    },

    // ========== Integer Arithmetic ==========
    /// Integer addition: dst = a + b
    IntAdd {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Integer subtraction: dst = a - b
    IntSub {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Integer multiplication: dst = a * b
    IntMult {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Unsigned integer division: dst = a / b
    IntDiv {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Signed integer division: dst = a / b (signed)
    IntSDiv {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Unsigned integer remainder: dst = a % b
    IntRem {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Signed integer remainder: dst = a % b (signed)
    IntSRem {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Two's complement negation: dst = -src
    IntNegate { dst: Varnode, src: Varnode },

    /// Addition with carry: dst = a + b + carry
    IntCarry {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Signed carry (overflow): dst = overflow(a + b)
    IntSCarry {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Signed borrow: dst = borrow(a - b)
    IntSBorrow {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    // ========== Logical Operations ==========
    /// Bitwise AND: dst = a & b
    IntAnd {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Bitwise OR: dst = a | b
    IntOr {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Bitwise XOR: dst = a ^ b
    IntXor {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Bitwise NOT: dst = ~src
    IntNot { dst: Varnode, src: Varnode },

    // ========== Shift Operations ==========
    /// Left shift: dst = a << b
    IntLeft {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Logical right shift: dst = a >> b (unsigned)
    IntRight {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Arithmetic right shift: dst = a >> b (signed)
    IntSRight {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    // ========== Comparison Operations ==========
    /// Equality: dst = (a == b) ? 1 : 0
    IntEqual {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Inequality: dst = (a != b) ? 1 : 0
    IntNotEqual {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Unsigned less than: dst = (a < b) ? 1 : 0
    IntLess {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Signed less than: dst = (a < b) ? 1 : 0 (signed)
    IntSLess {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Unsigned less or equal: dst = (a <= b) ? 1 : 0
    IntLessEqual {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Signed less or equal: dst = (a <= b) ? 1 : 0 (signed)
    IntSLessEqual {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    // ========== Extension Operations ==========
    /// Zero extension: dst = zext(src)
    IntZExt { dst: Varnode, src: Varnode },

    /// Sign extension: dst = sext(src)
    IntSExt { dst: Varnode, src: Varnode },

    // ========== Boolean Operations ==========
    /// Boolean NOT: dst = !src
    BoolNot { dst: Varnode, src: Varnode },

    /// Boolean AND: dst = a && b
    BoolAnd {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Boolean OR: dst = a || b
    BoolOr {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Boolean XOR: dst = a ^^ b
    BoolXor {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    // ========== Bit Manipulation ==========
    /// Concatenate two values: dst = (a << b.size*8) | b
    Piece {
        dst: Varnode,
        hi: Varnode,
        lo: Varnode,
    },

    /// Extract a portion of a value: dst = src[offset:size]
    Subpiece {
        dst: Varnode,
        src: Varnode,
        offset: u32,
    },

    /// Population count (number of 1 bits): dst = popcount(src)
    PopCount { dst: Varnode, src: Varnode },

    /// Count leading zeros: dst = clz(src)
    Lzcount { dst: Varnode, src: Varnode },

    // ========== Control Flow ==========
    /// Unconditional branch to target
    Branch { target: Varnode },

    /// Conditional branch: if (cond) goto target
    CBranch { target: Varnode, cond: Varnode },

    /// Indirect branch: goto *target
    BranchInd { target: Varnode },

    /// Call a subroutine
    Call { target: Varnode },

    /// Indirect call: call *target
    CallInd { target: Varnode },

    /// Return from subroutine
    Return { target: Varnode },

    // ========== Floating Point ==========
    /// Float addition: dst = a + b
    FloatAdd {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Float subtraction: dst = a - b
    FloatSub {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Float multiplication: dst = a * b
    FloatMult {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Float division: dst = a / b
    FloatDiv {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Float negation: dst = -src
    FloatNeg { dst: Varnode, src: Varnode },

    /// Float absolute value: dst = |src|
    FloatAbs { dst: Varnode, src: Varnode },

    /// Float square root: dst = sqrt(src)
    FloatSqrt { dst: Varnode, src: Varnode },

    /// Float ceiling: dst = ceil(src)
    FloatCeil { dst: Varnode, src: Varnode },

    /// Float floor: dst = floor(src)
    FloatFloor { dst: Varnode, src: Varnode },

    /// Float round: dst = round(src)
    FloatRound { dst: Varnode, src: Varnode },

    /// Float is NaN: dst = isnan(src)
    FloatNaN { dst: Varnode, src: Varnode },

    /// Float equality: dst = (a == b) ? 1 : 0
    FloatEqual {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Float not equal: dst = (a != b) ? 1 : 0
    FloatNotEqual {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Float less than: dst = (a < b) ? 1 : 0
    FloatLess {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Float less or equal: dst = (a <= b) ? 1 : 0
    FloatLessEqual {
        dst: Varnode,
        a: Varnode,
        b: Varnode,
    },

    /// Convert int to float: dst = (float)src
    Int2Float { dst: Varnode, src: Varnode },

    /// Convert float to int: dst = (int)src
    Float2Int { dst: Varnode, src: Varnode },

    /// Convert float to different size float: dst = (float_new_size)src
    FloatFloat { dst: Varnode, src: Varnode },

    /// Truncate float to int: dst = trunc(src)
    Trunc { dst: Varnode, src: Varnode },

    // ========== Special Operations ==========
    /// Call a user-defined operation (CALLOTHER in P-code)
    CallOther {
        /// Optional output varnode
        output: Option<Varnode>,
        /// User-defined operation index
        userop: u32,
        /// Input arguments
        inputs: Vec<Varnode>,
    },

    /// No operation (placeholder)
    Nop,

    /// Unimplemented instruction
    Unimplemented,

    /// CPU identification (CPUID-like)
    CpuId { dst: Varnode },

    /// Insert a breakpoint
    Breakpoint,

    /// Multiequal (SSA phi function, used in analysis)
    Multiequal { dst: Varnode, inputs: Vec<Varnode> },

    /// Indirect reference (used in analysis)
    Indirect {
        dst: Varnode,
        src: Varnode,
        indirect: Varnode,
    },

    /// Pointer addition: dst = base + (index * element_size)
    PtrAdd {
        dst: Varnode,
        base: Varnode,
        index: Varnode,
        element_size: u32,
    },

    /// Pointer subtraction: dst = base - (index * element_size)
    PtrSub {
        dst: Varnode,
        base: Varnode,
        index: Varnode,
        element_size: u32,
    },

    /// Segment calculation: dst = segment:offset
    SegmentOp {
        dst: Varnode,
        segment: Varnode,
        offset: Varnode,
    },

    /// New (allocation, used in high-level analysis)
    New { dst: Varnode, src: Varnode },

    /// Cast (type cast, used in high-level analysis)
    Cast { dst: Varnode, src: Varnode },

    /// Extract (bit field extraction)
    Extract {
        dst: Varnode,
        src: Varnode,
        position: Varnode,
    },

    /// Insert (bit field insertion)
    Insert {
        dst: Varnode,
        src: Varnode,
        value: Varnode,
        position: Varnode,
    },

    /// Conditional value merge produced when instruction-local P-code control
    /// flow is normalized into the linear r2il value graph.
    Select {
        dst: Varnode,
        cond: Varnode,
        if_true: Varnode,
        if_false: Varnode,
    },
}

impl R2ILOp {
    /// Returns true if this operation is a control flow operation.
    pub fn is_control_flow(&self) -> bool {
        matches!(
            self,
            R2ILOp::Branch { .. }
                | R2ILOp::CBranch { .. }
                | R2ILOp::BranchInd { .. }
                | R2ILOp::Call { .. }
                | R2ILOp::CallInd { .. }
                | R2ILOp::Return { .. }
        )
    }

    /// Returns true if this operation reads from memory.
    pub fn is_memory_read(&self) -> bool {
        matches!(
            self,
            R2ILOp::Load { .. }
                | R2ILOp::LoadLinked { .. }
                | R2ILOp::LoadGuarded { .. }
                | R2ILOp::AtomicCAS { .. }
        )
    }

    /// Returns true if this operation writes to memory.
    pub fn is_memory_write(&self) -> bool {
        matches!(
            self,
            R2ILOp::Store { .. }
                | R2ILOp::StoreConditional { .. }
                | R2ILOp::StoreGuarded { .. }
                | R2ILOp::AtomicCAS { .. }
        )
    }

    /// Returns true when this value operation may be evaluated speculatively.
    ///
    /// This is intentionally narrower than "has an output": reads, writes,
    /// allocation, CPU state queries, calls, and control flow may be observable
    /// even when their result is later discarded.
    pub fn is_speculatable_value(&self) -> bool {
        self.output().is_some()
            && !self.is_control_flow()
            && !self.is_memory_read()
            && !self.is_memory_write()
            && !matches!(
                self,
                R2ILOp::CallOther { .. } | R2ILOp::CpuId { .. } | R2ILOp::New { .. }
            )
    }

    /// Returns the output varnode if this operation has one.
    pub fn output(&self) -> Option<&Varnode> {
        match self {
            R2ILOp::Copy { dst, .. }
            | R2ILOp::Load { dst, .. }
            | R2ILOp::LoadLinked { dst, .. }
            | R2ILOp::LoadGuarded { dst, .. }
            | R2ILOp::AtomicCAS { dst, .. }
            | R2ILOp::IntAdd { dst, .. }
            | R2ILOp::IntSub { dst, .. }
            | R2ILOp::IntMult { dst, .. }
            | R2ILOp::IntDiv { dst, .. }
            | R2ILOp::IntSDiv { dst, .. }
            | R2ILOp::IntRem { dst, .. }
            | R2ILOp::IntSRem { dst, .. }
            | R2ILOp::IntNegate { dst, .. }
            | R2ILOp::IntCarry { dst, .. }
            | R2ILOp::IntSCarry { dst, .. }
            | R2ILOp::IntSBorrow { dst, .. }
            | R2ILOp::IntAnd { dst, .. }
            | R2ILOp::IntOr { dst, .. }
            | R2ILOp::IntXor { dst, .. }
            | R2ILOp::IntNot { dst, .. }
            | R2ILOp::IntLeft { dst, .. }
            | R2ILOp::IntRight { dst, .. }
            | R2ILOp::IntSRight { dst, .. }
            | R2ILOp::IntEqual { dst, .. }
            | R2ILOp::IntNotEqual { dst, .. }
            | R2ILOp::IntLess { dst, .. }
            | R2ILOp::IntSLess { dst, .. }
            | R2ILOp::IntLessEqual { dst, .. }
            | R2ILOp::IntSLessEqual { dst, .. }
            | R2ILOp::IntZExt { dst, .. }
            | R2ILOp::IntSExt { dst, .. }
            | R2ILOp::BoolNot { dst, .. }
            | R2ILOp::BoolAnd { dst, .. }
            | R2ILOp::BoolOr { dst, .. }
            | R2ILOp::BoolXor { dst, .. }
            | R2ILOp::Piece { dst, .. }
            | R2ILOp::Subpiece { dst, .. }
            | R2ILOp::PopCount { dst, .. }
            | R2ILOp::Lzcount { dst, .. }
            | R2ILOp::FloatAdd { dst, .. }
            | R2ILOp::FloatSub { dst, .. }
            | R2ILOp::FloatMult { dst, .. }
            | R2ILOp::FloatDiv { dst, .. }
            | R2ILOp::FloatNeg { dst, .. }
            | R2ILOp::FloatAbs { dst, .. }
            | R2ILOp::FloatSqrt { dst, .. }
            | R2ILOp::FloatCeil { dst, .. }
            | R2ILOp::FloatFloor { dst, .. }
            | R2ILOp::FloatRound { dst, .. }
            | R2ILOp::FloatNaN { dst, .. }
            | R2ILOp::FloatEqual { dst, .. }
            | R2ILOp::FloatNotEqual { dst, .. }
            | R2ILOp::FloatLess { dst, .. }
            | R2ILOp::FloatLessEqual { dst, .. }
            | R2ILOp::Int2Float { dst, .. }
            | R2ILOp::Float2Int { dst, .. }
            | R2ILOp::FloatFloat { dst, .. }
            | R2ILOp::Trunc { dst, .. }
            | R2ILOp::CpuId { dst }
            | R2ILOp::Multiequal { dst, .. }
            | R2ILOp::Indirect { dst, .. }
            | R2ILOp::PtrAdd { dst, .. }
            | R2ILOp::PtrSub { dst, .. }
            | R2ILOp::SegmentOp { dst, .. }
            | R2ILOp::New { dst, .. }
            | R2ILOp::Cast { dst, .. }
            | R2ILOp::Extract { dst, .. }
            | R2ILOp::Insert { dst, .. }
            | R2ILOp::Select { dst, .. } => Some(dst),
            R2ILOp::StoreConditional { result, .. } => result.as_ref(),
            R2ILOp::CallOther { output, .. } => output.as_ref(),
            _ => None,
        }
    }

    /// Returns the output varnode mutably if this operation has one.
    pub fn output_mut(&mut self) -> Option<&mut Varnode> {
        match self {
            R2ILOp::Copy { dst, .. }
            | R2ILOp::Load { dst, .. }
            | R2ILOp::LoadLinked { dst, .. }
            | R2ILOp::LoadGuarded { dst, .. }
            | R2ILOp::AtomicCAS { dst, .. }
            | R2ILOp::IntAdd { dst, .. }
            | R2ILOp::IntSub { dst, .. }
            | R2ILOp::IntMult { dst, .. }
            | R2ILOp::IntDiv { dst, .. }
            | R2ILOp::IntSDiv { dst, .. }
            | R2ILOp::IntRem { dst, .. }
            | R2ILOp::IntSRem { dst, .. }
            | R2ILOp::IntNegate { dst, .. }
            | R2ILOp::IntCarry { dst, .. }
            | R2ILOp::IntSCarry { dst, .. }
            | R2ILOp::IntSBorrow { dst, .. }
            | R2ILOp::IntAnd { dst, .. }
            | R2ILOp::IntOr { dst, .. }
            | R2ILOp::IntXor { dst, .. }
            | R2ILOp::IntNot { dst, .. }
            | R2ILOp::IntLeft { dst, .. }
            | R2ILOp::IntRight { dst, .. }
            | R2ILOp::IntSRight { dst, .. }
            | R2ILOp::IntEqual { dst, .. }
            | R2ILOp::IntNotEqual { dst, .. }
            | R2ILOp::IntLess { dst, .. }
            | R2ILOp::IntSLess { dst, .. }
            | R2ILOp::IntLessEqual { dst, .. }
            | R2ILOp::IntSLessEqual { dst, .. }
            | R2ILOp::IntZExt { dst, .. }
            | R2ILOp::IntSExt { dst, .. }
            | R2ILOp::BoolNot { dst, .. }
            | R2ILOp::BoolAnd { dst, .. }
            | R2ILOp::BoolOr { dst, .. }
            | R2ILOp::BoolXor { dst, .. }
            | R2ILOp::Piece { dst, .. }
            | R2ILOp::Subpiece { dst, .. }
            | R2ILOp::PopCount { dst, .. }
            | R2ILOp::Lzcount { dst, .. }
            | R2ILOp::FloatAdd { dst, .. }
            | R2ILOp::FloatSub { dst, .. }
            | R2ILOp::FloatMult { dst, .. }
            | R2ILOp::FloatDiv { dst, .. }
            | R2ILOp::FloatNeg { dst, .. }
            | R2ILOp::FloatAbs { dst, .. }
            | R2ILOp::FloatSqrt { dst, .. }
            | R2ILOp::FloatCeil { dst, .. }
            | R2ILOp::FloatFloor { dst, .. }
            | R2ILOp::FloatRound { dst, .. }
            | R2ILOp::FloatNaN { dst, .. }
            | R2ILOp::FloatEqual { dst, .. }
            | R2ILOp::FloatNotEqual { dst, .. }
            | R2ILOp::FloatLess { dst, .. }
            | R2ILOp::FloatLessEqual { dst, .. }
            | R2ILOp::Int2Float { dst, .. }
            | R2ILOp::Float2Int { dst, .. }
            | R2ILOp::FloatFloat { dst, .. }
            | R2ILOp::Trunc { dst, .. }
            | R2ILOp::CpuId { dst }
            | R2ILOp::Multiequal { dst, .. }
            | R2ILOp::Indirect { dst, .. }
            | R2ILOp::PtrAdd { dst, .. }
            | R2ILOp::PtrSub { dst, .. }
            | R2ILOp::SegmentOp { dst, .. }
            | R2ILOp::New { dst, .. }
            | R2ILOp::Cast { dst, .. }
            | R2ILOp::Extract { dst, .. }
            | R2ILOp::Insert { dst, .. }
            | R2ILOp::Select { dst, .. } => Some(dst),
            R2ILOp::StoreConditional { result, .. } => result.as_mut(),
            R2ILOp::CallOther { output, .. } => output.as_mut(),
            _ => None,
        }
    }

    /// Returns the input varnodes for this operation.
    ///
    /// This is the symmetric counterpart to `output()`, enabling consumers
    /// to iterate over all inputs without pattern matching on every variant.
    pub fn inputs(&self) -> Vec<&Varnode> {
        match self {
            // Data movement
            R2ILOp::Copy { src, .. } => vec![src],
            R2ILOp::Load { addr, .. } => vec![addr],
            R2ILOp::Store { addr, val, .. } => vec![addr, val],
            R2ILOp::Fence { .. } => vec![],
            R2ILOp::LoadLinked { addr, .. } => vec![addr],
            R2ILOp::StoreConditional { addr, val, .. } => vec![addr, val],
            R2ILOp::AtomicCAS {
                addr,
                expected,
                replacement,
                ..
            } => vec![addr, expected, replacement],
            R2ILOp::LoadGuarded { addr, guard, .. } => vec![addr, guard],
            R2ILOp::StoreGuarded {
                addr, val, guard, ..
            } => vec![addr, val, guard],

            // Binary integer operations
            R2ILOp::IntAdd { a, b, .. }
            | R2ILOp::IntSub { a, b, .. }
            | R2ILOp::IntMult { a, b, .. }
            | R2ILOp::IntDiv { a, b, .. }
            | R2ILOp::IntSDiv { a, b, .. }
            | R2ILOp::IntRem { a, b, .. }
            | R2ILOp::IntSRem { a, b, .. }
            | R2ILOp::IntCarry { a, b, .. }
            | R2ILOp::IntSCarry { a, b, .. }
            | R2ILOp::IntSBorrow { a, b, .. }
            | R2ILOp::IntAnd { a, b, .. }
            | R2ILOp::IntOr { a, b, .. }
            | R2ILOp::IntXor { a, b, .. }
            | R2ILOp::IntLeft { a, b, .. }
            | R2ILOp::IntRight { a, b, .. }
            | R2ILOp::IntSRight { a, b, .. }
            | R2ILOp::IntEqual { a, b, .. }
            | R2ILOp::IntNotEqual { a, b, .. }
            | R2ILOp::IntLess { a, b, .. }
            | R2ILOp::IntSLess { a, b, .. }
            | R2ILOp::IntLessEqual { a, b, .. }
            | R2ILOp::IntSLessEqual { a, b, .. } => vec![a, b],

            // Unary integer operations
            R2ILOp::IntNegate { src, .. }
            | R2ILOp::IntNot { src, .. }
            | R2ILOp::IntZExt { src, .. }
            | R2ILOp::IntSExt { src, .. } => vec![src],

            // Boolean operations
            R2ILOp::BoolNot { src, .. } => vec![src],
            R2ILOp::BoolAnd { a, b, .. }
            | R2ILOp::BoolOr { a, b, .. }
            | R2ILOp::BoolXor { a, b, .. } => vec![a, b],

            // Bit manipulation
            R2ILOp::Piece { hi, lo, .. } => vec![hi, lo],
            R2ILOp::Subpiece { src, .. } => vec![src],
            R2ILOp::PopCount { src, .. } | R2ILOp::Lzcount { src, .. } => vec![src],

            // Control flow
            R2ILOp::Branch { target } => vec![target],
            R2ILOp::CBranch { target, cond } => vec![target, cond],
            R2ILOp::BranchInd { target } => vec![target],
            R2ILOp::Call { target } => vec![target],
            R2ILOp::CallInd { target } => vec![target],
            R2ILOp::Return { target } => vec![target],

            // Binary float operations
            R2ILOp::FloatAdd { a, b, .. }
            | R2ILOp::FloatSub { a, b, .. }
            | R2ILOp::FloatMult { a, b, .. }
            | R2ILOp::FloatDiv { a, b, .. }
            | R2ILOp::FloatEqual { a, b, .. }
            | R2ILOp::FloatNotEqual { a, b, .. }
            | R2ILOp::FloatLess { a, b, .. }
            | R2ILOp::FloatLessEqual { a, b, .. } => vec![a, b],

            // Unary float operations
            R2ILOp::FloatNeg { src, .. }
            | R2ILOp::FloatAbs { src, .. }
            | R2ILOp::FloatSqrt { src, .. }
            | R2ILOp::FloatCeil { src, .. }
            | R2ILOp::FloatFloor { src, .. }
            | R2ILOp::FloatRound { src, .. }
            | R2ILOp::FloatNaN { src, .. }
            | R2ILOp::Int2Float { src, .. }
            | R2ILOp::Float2Int { src, .. }
            | R2ILOp::FloatFloat { src, .. }
            | R2ILOp::Trunc { src, .. } => vec![src],

            // Special operations
            R2ILOp::CallOther { inputs, .. } => inputs.iter().collect(),
            R2ILOp::Nop | R2ILOp::Unimplemented | R2ILOp::Breakpoint => vec![],
            R2ILOp::CpuId { .. } => vec![],
            R2ILOp::Multiequal { inputs, .. } => inputs.iter().collect(),
            R2ILOp::Indirect { src, indirect, .. } => vec![src, indirect],
            R2ILOp::PtrAdd { base, index, .. } | R2ILOp::PtrSub { base, index, .. } => {
                vec![base, index]
            }
            R2ILOp::SegmentOp {
                segment, offset, ..
            } => vec![segment, offset],
            R2ILOp::New { src, .. } | R2ILOp::Cast { src, .. } => vec![src],
            R2ILOp::Extract { src, position, .. } => vec![src, position],
            R2ILOp::Insert {
                src,
                value,
                position,
                ..
            } => vec![src, value, position],
            R2ILOp::Select {
                cond,
                if_true,
                if_false,
                ..
            } => vec![cond, if_true, if_false],
        }
    }

    /// Returns mutable references to the input varnodes for this operation.
    ///
    /// This enables transformation passes to modify operands in-place.
    pub fn inputs_mut(&mut self) -> Vec<&mut Varnode> {
        match self {
            // Data movement
            R2ILOp::Copy { src, .. } => vec![src],
            R2ILOp::Load { addr, .. } => vec![addr],
            R2ILOp::Store { addr, val, .. } => vec![addr, val],
            R2ILOp::Fence { .. } => vec![],
            R2ILOp::LoadLinked { addr, .. } => vec![addr],
            R2ILOp::StoreConditional { addr, val, .. } => vec![addr, val],
            R2ILOp::AtomicCAS {
                addr,
                expected,
                replacement,
                ..
            } => vec![addr, expected, replacement],
            R2ILOp::LoadGuarded { addr, guard, .. } => vec![addr, guard],
            R2ILOp::StoreGuarded {
                addr, val, guard, ..
            } => vec![addr, val, guard],

            // Binary integer operations
            R2ILOp::IntAdd { a, b, .. }
            | R2ILOp::IntSub { a, b, .. }
            | R2ILOp::IntMult { a, b, .. }
            | R2ILOp::IntDiv { a, b, .. }
            | R2ILOp::IntSDiv { a, b, .. }
            | R2ILOp::IntRem { a, b, .. }
            | R2ILOp::IntSRem { a, b, .. }
            | R2ILOp::IntCarry { a, b, .. }
            | R2ILOp::IntSCarry { a, b, .. }
            | R2ILOp::IntSBorrow { a, b, .. }
            | R2ILOp::IntAnd { a, b, .. }
            | R2ILOp::IntOr { a, b, .. }
            | R2ILOp::IntXor { a, b, .. }
            | R2ILOp::IntLeft { a, b, .. }
            | R2ILOp::IntRight { a, b, .. }
            | R2ILOp::IntSRight { a, b, .. }
            | R2ILOp::IntEqual { a, b, .. }
            | R2ILOp::IntNotEqual { a, b, .. }
            | R2ILOp::IntLess { a, b, .. }
            | R2ILOp::IntSLess { a, b, .. }
            | R2ILOp::IntLessEqual { a, b, .. }
            | R2ILOp::IntSLessEqual { a, b, .. } => vec![a, b],

            // Unary integer operations
            R2ILOp::IntNegate { src, .. }
            | R2ILOp::IntNot { src, .. }
            | R2ILOp::IntZExt { src, .. }
            | R2ILOp::IntSExt { src, .. } => vec![src],

            // Boolean operations
            R2ILOp::BoolNot { src, .. } => vec![src],
            R2ILOp::BoolAnd { a, b, .. }
            | R2ILOp::BoolOr { a, b, .. }
            | R2ILOp::BoolXor { a, b, .. } => vec![a, b],

            // Bit manipulation
            R2ILOp::Piece { hi, lo, .. } => vec![hi, lo],
            R2ILOp::Subpiece { src, .. } => vec![src],
            R2ILOp::PopCount { src, .. } | R2ILOp::Lzcount { src, .. } => vec![src],

            // Control flow
            R2ILOp::Branch { target } => vec![target],
            R2ILOp::CBranch { target, cond } => vec![target, cond],
            R2ILOp::BranchInd { target } => vec![target],
            R2ILOp::Call { target } => vec![target],
            R2ILOp::CallInd { target } => vec![target],
            R2ILOp::Return { target } => vec![target],

            // Binary float operations
            R2ILOp::FloatAdd { a, b, .. }
            | R2ILOp::FloatSub { a, b, .. }
            | R2ILOp::FloatMult { a, b, .. }
            | R2ILOp::FloatDiv { a, b, .. }
            | R2ILOp::FloatEqual { a, b, .. }
            | R2ILOp::FloatNotEqual { a, b, .. }
            | R2ILOp::FloatLess { a, b, .. }
            | R2ILOp::FloatLessEqual { a, b, .. } => vec![a, b],

            // Unary float operations
            R2ILOp::FloatNeg { src, .. }
            | R2ILOp::FloatAbs { src, .. }
            | R2ILOp::FloatSqrt { src, .. }
            | R2ILOp::FloatCeil { src, .. }
            | R2ILOp::FloatFloor { src, .. }
            | R2ILOp::FloatRound { src, .. }
            | R2ILOp::FloatNaN { src, .. }
            | R2ILOp::Int2Float { src, .. }
            | R2ILOp::Float2Int { src, .. }
            | R2ILOp::FloatFloat { src, .. }
            | R2ILOp::Trunc { src, .. } => vec![src],

            // Special operations
            R2ILOp::CallOther { inputs, .. } => inputs.iter_mut().collect(),
            R2ILOp::Nop | R2ILOp::Unimplemented | R2ILOp::Breakpoint => vec![],
            R2ILOp::CpuId { .. } => vec![],
            R2ILOp::Multiequal { inputs, .. } => inputs.iter_mut().collect(),
            R2ILOp::Indirect { src, indirect, .. } => vec![src, indirect],
            R2ILOp::PtrAdd { base, index, .. } | R2ILOp::PtrSub { base, index, .. } => {
                vec![base, index]
            }
            R2ILOp::SegmentOp {
                segment, offset, ..
            } => vec![segment, offset],
            R2ILOp::New { src, .. } | R2ILOp::Cast { src, .. } => vec![src],
            R2ILOp::Extract { src, position, .. } => vec![src, position],
            R2ILOp::Insert {
                src,
                value,
                position,
                ..
            } => vec![src, value, position],
            R2ILOp::Select {
                cond,
                if_true,
                if_false,
                ..
            } => vec![cond, if_true, if_false],
        }
    }
}

impl std::fmt::Display for R2ILOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // Data movement
            R2ILOp::Copy { dst, src } => write!(f, "{} = COPY {}", dst, src),
            R2ILOp::Load { dst, space, addr } => {
                write!(f, "{} = LOAD [{}]{}", dst, space, addr)
            }
            R2ILOp::Store { space, addr, val } => {
                write!(f, "STORE [{}]{} = {}", space, addr, val)
            }
            R2ILOp::Fence { ordering } => write!(f, "FENCE({ordering:?})"),
            R2ILOp::LoadLinked {
                dst,
                space,
                addr,
                ordering,
            } => {
                write!(
                    f,
                    "{} = LOAD_LINKED [{}]{} ({ordering:?})",
                    dst, space, addr
                )
            }
            R2ILOp::StoreConditional {
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
                    "STORE_CONDITIONAL [{}]{} = {} ({ordering:?})",
                    space, addr, val
                )
            }
            R2ILOp::AtomicCAS {
                dst,
                space,
                addr,
                expected,
                replacement,
                ordering,
            } => {
                write!(
                    f,
                    "{} = ATOMIC_CAS [{}]{}, {}, {} ({ordering:?})",
                    dst, space, addr, expected, replacement
                )
            }
            R2ILOp::LoadGuarded {
                dst,
                space,
                addr,
                guard,
                ordering,
            } => {
                write!(
                    f,
                    "{} = LOAD_GUARDED [{}]{}, {} ({ordering:?})",
                    dst, space, addr, guard
                )
            }
            R2ILOp::StoreGuarded {
                space,
                addr,
                val,
                guard,
                ordering,
            } => {
                write!(
                    f,
                    "STORE_GUARDED [{}]{} = {} if {} ({ordering:?})",
                    space, addr, val, guard
                )
            }

            // Integer arithmetic
            R2ILOp::IntAdd { dst, a, b } => write!(f, "{} = {} + {}", dst, a, b),
            R2ILOp::IntSub { dst, a, b } => write!(f, "{} = {} - {}", dst, a, b),
            R2ILOp::IntMult { dst, a, b } => write!(f, "{} = {} * {}", dst, a, b),
            R2ILOp::IntDiv { dst, a, b } => write!(f, "{} = {} / {}", dst, a, b),
            R2ILOp::IntSDiv { dst, a, b } => write!(f, "{} = {} s/ {}", dst, a, b),
            R2ILOp::IntRem { dst, a, b } => write!(f, "{} = {} % {}", dst, a, b),
            R2ILOp::IntSRem { dst, a, b } => write!(f, "{} = {} s% {}", dst, a, b),
            R2ILOp::IntNegate { dst, src } => write!(f, "{} = -{}", dst, src),
            R2ILOp::IntCarry { dst, a, b } => write!(f, "{} = CARRY({}, {})", dst, a, b),
            R2ILOp::IntSCarry { dst, a, b } => write!(f, "{} = SCARRY({}, {})", dst, a, b),
            R2ILOp::IntSBorrow { dst, a, b } => write!(f, "{} = SBORROW({}, {})", dst, a, b),

            // Logical operations
            R2ILOp::IntAnd { dst, a, b } => write!(f, "{} = {} & {}", dst, a, b),
            R2ILOp::IntOr { dst, a, b } => write!(f, "{} = {} | {}", dst, a, b),
            R2ILOp::IntXor { dst, a, b } => write!(f, "{} = {} ^ {}", dst, a, b),
            R2ILOp::IntNot { dst, src } => write!(f, "{} = ~{}", dst, src),

            // Shift operations
            R2ILOp::IntLeft { dst, a, b } => write!(f, "{} = {} << {}", dst, a, b),
            R2ILOp::IntRight { dst, a, b } => write!(f, "{} = {} >> {}", dst, a, b),
            R2ILOp::IntSRight { dst, a, b } => write!(f, "{} = {} s>> {}", dst, a, b),

            // Comparison operations
            R2ILOp::IntEqual { dst, a, b } => write!(f, "{} = {} == {}", dst, a, b),
            R2ILOp::IntNotEqual { dst, a, b } => write!(f, "{} = {} != {}", dst, a, b),
            R2ILOp::IntLess { dst, a, b } => write!(f, "{} = {} < {}", dst, a, b),
            R2ILOp::IntSLess { dst, a, b } => write!(f, "{} = {} s< {}", dst, a, b),
            R2ILOp::IntLessEqual { dst, a, b } => write!(f, "{} = {} <= {}", dst, a, b),
            R2ILOp::IntSLessEqual { dst, a, b } => write!(f, "{} = {} s<= {}", dst, a, b),

            // Extension operations
            R2ILOp::IntZExt { dst, src } => write!(f, "{} = ZEXT({})", dst, src),
            R2ILOp::IntSExt { dst, src } => write!(f, "{} = SEXT({})", dst, src),

            // Boolean operations
            R2ILOp::BoolNot { dst, src } => write!(f, "{} = !{}", dst, src),
            R2ILOp::BoolAnd { dst, a, b } => write!(f, "{} = {} && {}", dst, a, b),
            R2ILOp::BoolOr { dst, a, b } => write!(f, "{} = {} || {}", dst, a, b),
            R2ILOp::BoolXor { dst, a, b } => write!(f, "{} = {} ^^ {}", dst, a, b),

            // Bit manipulation
            R2ILOp::Piece { dst, hi, lo } => write!(f, "{} = PIECE({}, {})", dst, hi, lo),
            R2ILOp::Subpiece { dst, src, offset } => {
                write!(f, "{} = SUBPIECE({}, {})", dst, src, offset)
            }
            R2ILOp::PopCount { dst, src } => write!(f, "{} = POPCOUNT({})", dst, src),
            R2ILOp::Lzcount { dst, src } => write!(f, "{} = LZCOUNT({})", dst, src),

            // Control flow
            R2ILOp::Branch { target } => write!(f, "BRANCH {}", target),
            R2ILOp::CBranch { target, cond } => write!(f, "CBRANCH {} if {}", target, cond),
            R2ILOp::BranchInd { target } => write!(f, "BRANCHIND {}", target),
            R2ILOp::Call { target } => write!(f, "CALL {}", target),
            R2ILOp::CallInd { target } => write!(f, "CALLIND {}", target),
            R2ILOp::Return { target } => write!(f, "RETURN {}", target),

            // Floating point operations
            R2ILOp::FloatAdd { dst, a, b } => write!(f, "{} = {} f+ {}", dst, a, b),
            R2ILOp::FloatSub { dst, a, b } => write!(f, "{} = {} f- {}", dst, a, b),
            R2ILOp::FloatMult { dst, a, b } => write!(f, "{} = {} f* {}", dst, a, b),
            R2ILOp::FloatDiv { dst, a, b } => write!(f, "{} = {} f/ {}", dst, a, b),
            R2ILOp::FloatNeg { dst, src } => write!(f, "{} = f-{}", dst, src),
            R2ILOp::FloatAbs { dst, src } => write!(f, "{} = FABS({})", dst, src),
            R2ILOp::FloatSqrt { dst, src } => write!(f, "{} = FSQRT({})", dst, src),
            R2ILOp::FloatCeil { dst, src } => write!(f, "{} = FCEIL({})", dst, src),
            R2ILOp::FloatFloor { dst, src } => write!(f, "{} = FFLOOR({})", dst, src),
            R2ILOp::FloatRound { dst, src } => write!(f, "{} = FROUND({})", dst, src),
            R2ILOp::FloatNaN { dst, src } => write!(f, "{} = FNAN({})", dst, src),
            R2ILOp::FloatEqual { dst, a, b } => write!(f, "{} = {} f== {}", dst, a, b),
            R2ILOp::FloatNotEqual { dst, a, b } => write!(f, "{} = {} f!= {}", dst, a, b),
            R2ILOp::FloatLess { dst, a, b } => write!(f, "{} = {} f< {}", dst, a, b),
            R2ILOp::FloatLessEqual { dst, a, b } => write!(f, "{} = {} f<= {}", dst, a, b),
            R2ILOp::Int2Float { dst, src } => write!(f, "{} = INT2FLOAT({})", dst, src),
            R2ILOp::Float2Int { dst, src } => write!(f, "{} = FLOAT2INT({})", dst, src),
            R2ILOp::FloatFloat { dst, src } => write!(f, "{} = FLOAT2FLOAT({})", dst, src),
            R2ILOp::Trunc { dst, src } => write!(f, "{} = TRUNC({})", dst, src),

            // Special operations
            R2ILOp::CallOther {
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
            R2ILOp::Nop => write!(f, "NOP"),
            R2ILOp::Unimplemented => write!(f, "UNIMPLEMENTED"),
            R2ILOp::CpuId { dst } => write!(f, "{} = CPUID", dst),
            R2ILOp::Breakpoint => write!(f, "BREAKPOINT"),
            R2ILOp::Multiequal { dst, inputs } => {
                write!(f, "{} = PHI(", dst)?;
                for (i, inp) in inputs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", inp)?;
                }
                write!(f, ")")
            }
            R2ILOp::Indirect { dst, src, indirect } => {
                write!(f, "{} = INDIRECT({}, {})", dst, src, indirect)
            }
            R2ILOp::PtrAdd {
                dst,
                base,
                index,
                element_size,
            } => {
                write!(f, "{} = PTRADD({}, {}, {})", dst, base, index, element_size)
            }
            R2ILOp::PtrSub {
                dst,
                base,
                index,
                element_size,
            } => {
                write!(f, "{} = PTRSUB({}, {}, {})", dst, base, index, element_size)
            }
            R2ILOp::SegmentOp {
                dst,
                segment,
                offset,
            } => {
                write!(f, "{} = SEGMENT({}, {})", dst, segment, offset)
            }
            R2ILOp::New { dst, src } => write!(f, "{} = NEW({})", dst, src),
            R2ILOp::Cast { dst, src } => write!(f, "{} = CAST({})", dst, src),
            R2ILOp::Extract { dst, src, position } => {
                write!(f, "{} = EXTRACT({}, {})", dst, src, position)
            }
            R2ILOp::Insert {
                dst,
                src,
                value,
                position,
            } => {
                write!(f, "{} = INSERT({}, {}, {})", dst, src, value, position)
            }
            R2ILOp::Select {
                dst,
                cond,
                if_true,
                if_false,
            } => write!(f, "{} = SELECT({}, {}, {})", dst, cond, if_true, if_false),
        }
    }
}

/// Information about a switch case.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SwitchCase {
    /// The case value.
    pub value: u64,
    /// The target address for this case.
    pub target: u64,
}

/// Information about a switch statement (jump table).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SwitchInfo {
    /// Address of the switch instruction.
    pub switch_addr: u64,
    /// Minimum case value.
    pub min_val: u64,
    /// Maximum case value.
    pub max_val: u64,
    /// Default case target (if any).
    pub default_target: Option<u64>,
    /// All switch cases.
    pub cases: Vec<SwitchCase>,
}

/// A sequence of r2il operations for a single instruction.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct R2ILBlock {
    /// The address of the instruction
    pub addr: u64,
    /// The size of the instruction in bytes
    pub size: u32,
    /// The operations for this instruction
    pub ops: Vec<R2ILOp>,
    /// Switch table information (if this block contains a switch).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub switch_info: Option<SwitchInfo>,
    /// Optional metadata for ops, keyed by operation index.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub op_metadata: BTreeMap<usize, OpMetadata>,
}

impl R2ILBlock {
    /// Create a new empty block.
    pub fn new(addr: u64, size: u32) -> Self {
        Self {
            addr,
            size,
            ops: Vec::new(),
            switch_info: None,
            op_metadata: BTreeMap::new(),
        }
    }

    /// Add an operation to this block.
    pub fn push(&mut self, op: R2ILOp) {
        self.ops.push(op);
    }

    /// Add an operation and optional metadata to this block.
    pub fn push_with_metadata(&mut self, op: R2ILOp, meta: Option<OpMetadata>) {
        let idx = self.ops.len();
        self.ops.push(op);
        if let Some(meta) = meta {
            self.op_metadata.insert(idx, meta);
        }
    }

    /// Set metadata for an operation index.
    pub fn set_op_metadata(&mut self, op_index: usize, meta: OpMetadata) {
        self.op_metadata.insert(op_index, meta);
    }

    /// Get metadata for an operation index.
    pub fn op_metadata(&self, op_index: usize) -> Option<&OpMetadata> {
        self.op_metadata.get(&op_index)
    }

    /// Remove metadata for an operation index.
    pub fn remove_op_metadata(&mut self, op_index: usize) -> Option<OpMetadata> {
        self.op_metadata.remove(&op_index)
    }

    /// Set the switch info for this block.
    pub fn set_switch_info(&mut self, info: SwitchInfo) {
        self.switch_info = Some(info);
    }
}
