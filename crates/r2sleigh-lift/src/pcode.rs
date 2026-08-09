//! P-code to r2il translation.
//!
//! This module maps Sleigh P-code operations to r2il opcodes.

use r2il::{R2ILOp, SpaceId, Varnode};
use thiserror::Error;

use crate::translate::{self, PcodeSource};

/// Errors that can occur during P-code translation.
#[derive(Debug, Error)]
pub enum PcodeError {
    #[error("Unknown P-code opcode: {0}")]
    UnknownOpcode(u32),

    #[error("Invalid opcode: {0}")]
    InvalidOpcode(String),

    #[error("Invalid operand count for {op}: expected {expected}, got {got}")]
    InvalidOperandCount {
        op: &'static str,
        expected: usize,
        got: usize,
    },

    #[error("Missing output operand for {0}")]
    MissingOutput(&'static str),

    #[error("Invalid space ID: {0}")]
    InvalidSpace(u64),
}

/// Result type for P-code translation.
pub type Result<T> = std::result::Result<T, PcodeError>;

/// P-code opcode constants (matching Ghidra's definitions).
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PcodeOp {
    Copy = 1,
    Load = 2,
    Store = 3,
    Branch = 4,
    CBranch = 5,
    BranchInd = 6,
    Call = 7,
    CallInd = 8,
    CallOther = 9,
    Return = 10,

    IntEqual = 11,
    IntNotEqual = 12,
    IntSLess = 13,
    IntSLessEqual = 14,
    IntLess = 15,
    IntLessEqual = 16,
    IntZExt = 17,
    IntSExt = 18,
    IntAdd = 19,
    IntSub = 20,
    IntCarry = 21,
    IntSCarry = 22,
    IntSBorrow = 23,
    Int2Comp = 24,
    IntNegate = 25,
    IntXor = 26,
    IntAnd = 27,
    IntOr = 28,
    IntLeft = 29,
    IntRight = 30,
    IntSRight = 31,
    IntMult = 32,
    IntDiv = 33,
    IntSDiv = 34,
    IntRem = 35,
    IntSRem = 36,

    BoolNot = 37,
    BoolXor = 38,
    BoolAnd = 39,
    BoolOr = 40,

    FloatEqual = 41,
    FloatNotEqual = 42,
    FloatLess = 43,
    FloatLessEqual = 44,
    FloatNaN = 46,
    FloatAdd = 47,
    FloatDiv = 48,
    FloatMult = 49,
    FloatSub = 50,
    FloatNeg = 51,
    FloatAbs = 52,
    FloatSqrt = 53,
    Int2Float = 54,
    Float2Int = 55,
    FloatFloat = 56,
    Trunc = 57,
    FloatCeil = 58,
    FloatFloor = 59,
    FloatRound = 60,

    Multiequal = 61,
    Indirect = 62,
    Piece = 63,
    Subpiece = 64,

    Cast = 65,
    PtrAdd = 66,
    PtrSub = 67,
    SegmentOp = 68,
    CpuId = 69,
    New = 70,

    Insert = 71,
    Extract = 72,
    PopCount = 73,
    Lzcount = 74,
}

impl PcodeOp {
    /// Try to convert a u32 to a PcodeOp.
    pub fn from_u32(value: u32) -> Option<Self> {
        match value {
            1 => Some(PcodeOp::Copy),
            2 => Some(PcodeOp::Load),
            3 => Some(PcodeOp::Store),
            4 => Some(PcodeOp::Branch),
            5 => Some(PcodeOp::CBranch),
            6 => Some(PcodeOp::BranchInd),
            7 => Some(PcodeOp::Call),
            8 => Some(PcodeOp::CallInd),
            9 => Some(PcodeOp::CallOther),
            10 => Some(PcodeOp::Return),
            11 => Some(PcodeOp::IntEqual),
            12 => Some(PcodeOp::IntNotEqual),
            13 => Some(PcodeOp::IntSLess),
            14 => Some(PcodeOp::IntSLessEqual),
            15 => Some(PcodeOp::IntLess),
            16 => Some(PcodeOp::IntLessEqual),
            17 => Some(PcodeOp::IntZExt),
            18 => Some(PcodeOp::IntSExt),
            19 => Some(PcodeOp::IntAdd),
            20 => Some(PcodeOp::IntSub),
            21 => Some(PcodeOp::IntCarry),
            22 => Some(PcodeOp::IntSCarry),
            23 => Some(PcodeOp::IntSBorrow),
            24 => Some(PcodeOp::Int2Comp),
            25 => Some(PcodeOp::IntNegate),
            26 => Some(PcodeOp::IntXor),
            27 => Some(PcodeOp::IntAnd),
            28 => Some(PcodeOp::IntOr),
            29 => Some(PcodeOp::IntLeft),
            30 => Some(PcodeOp::IntRight),
            31 => Some(PcodeOp::IntSRight),
            32 => Some(PcodeOp::IntMult),
            33 => Some(PcodeOp::IntDiv),
            34 => Some(PcodeOp::IntSDiv),
            35 => Some(PcodeOp::IntRem),
            36 => Some(PcodeOp::IntSRem),
            37 => Some(PcodeOp::BoolNot),
            38 => Some(PcodeOp::BoolXor),
            39 => Some(PcodeOp::BoolAnd),
            40 => Some(PcodeOp::BoolOr),
            41 => Some(PcodeOp::FloatEqual),
            42 => Some(PcodeOp::FloatNotEqual),
            43 => Some(PcodeOp::FloatLess),
            44 => Some(PcodeOp::FloatLessEqual),
            46 => Some(PcodeOp::FloatNaN),
            47 => Some(PcodeOp::FloatAdd),
            48 => Some(PcodeOp::FloatDiv),
            49 => Some(PcodeOp::FloatMult),
            50 => Some(PcodeOp::FloatSub),
            51 => Some(PcodeOp::FloatNeg),
            52 => Some(PcodeOp::FloatAbs),
            53 => Some(PcodeOp::FloatSqrt),
            54 => Some(PcodeOp::Int2Float),
            55 => Some(PcodeOp::Float2Int),
            56 => Some(PcodeOp::FloatFloat),
            57 => Some(PcodeOp::Trunc),
            58 => Some(PcodeOp::FloatCeil),
            59 => Some(PcodeOp::FloatFloor),
            60 => Some(PcodeOp::FloatRound),
            61 => Some(PcodeOp::Multiequal),
            62 => Some(PcodeOp::Indirect),
            63 => Some(PcodeOp::Piece),
            64 => Some(PcodeOp::Subpiece),
            65 => Some(PcodeOp::Cast),
            66 => Some(PcodeOp::PtrAdd),
            67 => Some(PcodeOp::PtrSub),
            68 => Some(PcodeOp::SegmentOp),
            69 => Some(PcodeOp::CpuId),
            70 => Some(PcodeOp::New),
            71 => Some(PcodeOp::Insert),
            72 => Some(PcodeOp::Extract),
            73 => Some(PcodeOp::PopCount),
            74 => Some(PcodeOp::Lzcount),
            _ => None,
        }
    }
}

/// A raw P-code varnode from Sleigh.
#[derive(Debug, Clone)]
pub struct RawVarnode {
    /// Space index (from Sleigh)
    pub space_idx: u32,
    /// Offset within the space
    pub offset: u64,
    /// Size in bytes
    pub size: u32,
}

impl RawVarnode {
    /// Create a new raw varnode.
    pub fn new(space_idx: u32, offset: u64, size: u32) -> Self {
        Self {
            space_idx,
            offset,
            size,
        }
    }
}

/// A raw P-code operation from Sleigh.
#[derive(Debug, Clone)]
pub struct RawPcodeOp {
    /// Opcode
    pub opcode: u32,
    /// Output varnode (if any)
    pub output: Option<RawVarnode>,
    /// Input varnodes
    pub inputs: Vec<RawVarnode>,
}

/// Wrapper for RawPcodeOp that implements PcodeSource.
///
/// This allows using the shared translation functions from the translate module.
struct RawPcodeSourceWrapper<'a> {
    raw: &'a RawPcodeOp,
    translator: &'a PcodeTranslator,
}

impl<'a> PcodeSource for RawPcodeSourceWrapper<'a> {
    fn output(&self) -> Option<Varnode> {
        self.raw
            .output
            .as_ref()
            .and_then(|v| self.translator.convert_varnode(v).ok())
    }

    fn input(&self, idx: usize) -> Option<Varnode> {
        self.raw
            .inputs
            .get(idx)
            .and_then(|v| self.translator.convert_varnode(v).ok())
    }

    fn input_raw_offset(&self, idx: usize) -> Option<u64> {
        self.raw.inputs.get(idx).map(|v| v.offset)
    }

    fn input_count(&self) -> usize {
        self.raw.inputs.len()
    }

    fn space_from_index(&self, idx: u64) -> Option<SpaceId> {
        usize::try_from(idx)
            .ok()
            .and_then(|idx| self.translator.space_map.get(idx))
            .copied()
    }
}

/// Translator from P-code to r2il.
pub struct PcodeTranslator {
    /// Mapping from Sleigh space indices to r2il SpaceId
    space_map: Vec<SpaceId>,
}

impl PcodeTranslator {
    /// Create a new translator with the given space mapping.
    pub fn new(space_map: Vec<SpaceId>) -> Self {
        Self { space_map }
    }

    /// Create a default translator with standard space mapping.
    pub fn default_spaces() -> Self {
        Self {
            space_map: vec![
                SpaceId::Const,    // 0: const
                SpaceId::Ram,      // 1: ram
                SpaceId::Register, // 2: register
                SpaceId::Unique,   // 3: unique
            ],
        }
    }

    /// Convert a raw varnode to an r2il Varnode.
    fn convert_varnode(&self, raw: &RawVarnode) -> Result<Varnode> {
        let space = self
            .space_map
            .get(raw.space_idx as usize)
            .copied()
            .unwrap_or(SpaceId::Custom(raw.space_idx));

        Ok(Varnode::new(space, raw.offset, raw.size))
    }

    /// Wrap a RawPcodeOp for use with shared translate functions.
    fn wrap<'a>(&'a self, raw: &'a RawPcodeOp) -> RawPcodeSourceWrapper<'a> {
        RawPcodeSourceWrapper {
            raw,
            translator: self,
        }
    }

    /// Translate a single P-code operation to r2il.
    pub fn translate(&self, raw: &RawPcodeOp) -> Result<R2ILOp> {
        let opcode = PcodeOp::from_u32(raw.opcode).ok_or(PcodeError::UnknownOpcode(raw.opcode))?;

        match opcode {
            PcodeOp::Copy => {
                let dst = self.require_output(raw, "COPY")?;
                let src = self.require_input(raw, 0, "COPY")?;
                Ok(R2ILOp::Copy { dst, src })
            }

            PcodeOp::Load => translate::translate_load(&self.wrap(raw)).map_err(translate_err),

            PcodeOp::Store => translate::translate_store(&self.wrap(raw)).map_err(translate_err),

            PcodeOp::Branch => {
                let target = self.require_input(raw, 0, "BRANCH")?;
                Ok(R2ILOp::Branch { target })
            }

            PcodeOp::CBranch => {
                // Use shared translate function for correct operand order
                translate::translate_cbranch(&self.wrap(raw)).map_err(translate_err)
            }

            PcodeOp::BranchInd => {
                let target = self.require_input(raw, 0, "BRANCHIND")?;
                Ok(R2ILOp::BranchInd { target })
            }

            PcodeOp::Call => {
                let target = self.require_input(raw, 0, "CALL")?;
                Ok(R2ILOp::Call { target })
            }

            PcodeOp::CallInd => {
                let target = self.require_input(raw, 0, "CALLIND")?;
                Ok(R2ILOp::CallInd { target })
            }

            PcodeOp::CallOther => {
                let userop_vn = self.require_raw_input(raw, 0, "CALLOTHER")?;
                let userop = userop_vn.offset as u32;
                let output = raw
                    .output
                    .as_ref()
                    .map(|o| self.convert_varnode(o))
                    .transpose()?;
                let inputs: Result<Vec<Varnode>> = raw.inputs[1..]
                    .iter()
                    .map(|v| self.convert_varnode(v))
                    .collect();
                Ok(R2ILOp::CallOther {
                    output,
                    userop,
                    inputs: inputs?,
                })
            }

            PcodeOp::Return => {
                let target = self.require_input(raw, 0, "RETURN")?;
                Ok(R2ILOp::Return { target })
            }

            // Integer comparison
            PcodeOp::IntEqual => {
                self.binary_op(raw, "INT_EQUAL", |dst, a, b| R2ILOp::IntEqual { dst, a, b })
            }
            PcodeOp::IntNotEqual => self.binary_op(raw, "INT_NOTEQUAL", |dst, a, b| {
                R2ILOp::IntNotEqual { dst, a, b }
            }),
            PcodeOp::IntSLess => {
                self.binary_op(raw, "INT_SLESS", |dst, a, b| R2ILOp::IntSLess { dst, a, b })
            }
            PcodeOp::IntSLessEqual => self.binary_op(raw, "INT_SLESSEQUAL", |dst, a, b| {
                R2ILOp::IntSLessEqual { dst, a, b }
            }),
            PcodeOp::IntLess => {
                self.binary_op(raw, "INT_LESS", |dst, a, b| R2ILOp::IntLess { dst, a, b })
            }
            PcodeOp::IntLessEqual => self.binary_op(raw, "INT_LESSEQUAL", |dst, a, b| {
                R2ILOp::IntLessEqual { dst, a, b }
            }),

            // Integer extension
            PcodeOp::IntZExt => {
                self.unary_op(raw, "INT_ZEXT", |dst, src| R2ILOp::IntZExt { dst, src })
            }
            PcodeOp::IntSExt => {
                self.unary_op(raw, "INT_SEXT", |dst, src| R2ILOp::IntSExt { dst, src })
            }

            // Integer arithmetic
            PcodeOp::IntAdd => {
                self.binary_op(raw, "INT_ADD", |dst, a, b| R2ILOp::IntAdd { dst, a, b })
            }
            PcodeOp::IntSub => {
                self.binary_op(raw, "INT_SUB", |dst, a, b| R2ILOp::IntSub { dst, a, b })
            }
            PcodeOp::IntCarry => {
                self.binary_op(raw, "INT_CARRY", |dst, a, b| R2ILOp::IntCarry { dst, a, b })
            }
            PcodeOp::IntSCarry => self.binary_op(raw, "INT_SCARRY", |dst, a, b| {
                R2ILOp::IntSCarry { dst, a, b }
            }),
            PcodeOp::IntSBorrow => self.binary_op(raw, "INT_SBORROW", |dst, a, b| {
                R2ILOp::IntSBorrow { dst, a, b }
            }),
            // Int2Comp (opcode 24) = two's complement negation
            PcodeOp::Int2Comp => {
                self.unary_op(raw, "INT_2COMP", |dst, src| R2ILOp::IntNegate { dst, src })
            }
            // IntNegate (opcode 25) = bitwise NOT (confusing Ghidra naming)
            PcodeOp::IntNegate => {
                self.unary_op(raw, "INT_NEGATE", |dst, src| R2ILOp::IntNot { dst, src })
            }
            PcodeOp::IntMult => {
                self.binary_op(raw, "INT_MULT", |dst, a, b| R2ILOp::IntMult { dst, a, b })
            }
            PcodeOp::IntDiv => {
                self.binary_op(raw, "INT_DIV", |dst, a, b| R2ILOp::IntDiv { dst, a, b })
            }
            PcodeOp::IntSDiv => {
                self.binary_op(raw, "INT_SDIV", |dst, a, b| R2ILOp::IntSDiv { dst, a, b })
            }
            PcodeOp::IntRem => {
                self.binary_op(raw, "INT_REM", |dst, a, b| R2ILOp::IntRem { dst, a, b })
            }
            PcodeOp::IntSRem => {
                self.binary_op(raw, "INT_SREM", |dst, a, b| R2ILOp::IntSRem { dst, a, b })
            }

            // Bitwise operations
            PcodeOp::IntXor => {
                self.binary_op(raw, "INT_XOR", |dst, a, b| R2ILOp::IntXor { dst, a, b })
            }
            PcodeOp::IntAnd => {
                self.binary_op(raw, "INT_AND", |dst, a, b| R2ILOp::IntAnd { dst, a, b })
            }
            PcodeOp::IntOr => {
                self.binary_op(raw, "INT_OR", |dst, a, b| R2ILOp::IntOr { dst, a, b })
            }
            PcodeOp::IntLeft => {
                self.binary_op(raw, "INT_LEFT", |dst, a, b| R2ILOp::IntLeft { dst, a, b })
            }
            PcodeOp::IntRight => {
                self.binary_op(raw, "INT_RIGHT", |dst, a, b| R2ILOp::IntRight { dst, a, b })
            }
            PcodeOp::IntSRight => self.binary_op(raw, "INT_SRIGHT", |dst, a, b| {
                R2ILOp::IntSRight { dst, a, b }
            }),

            // Boolean operations
            PcodeOp::BoolNot => {
                self.unary_op(raw, "BOOL_NEGATE", |dst, src| R2ILOp::BoolNot { dst, src })
            }
            PcodeOp::BoolXor => {
                self.binary_op(raw, "BOOL_XOR", |dst, a, b| R2ILOp::BoolXor { dst, a, b })
            }
            PcodeOp::BoolAnd => {
                self.binary_op(raw, "BOOL_AND", |dst, a, b| R2ILOp::BoolAnd { dst, a, b })
            }
            PcodeOp::BoolOr => {
                self.binary_op(raw, "BOOL_OR", |dst, a, b| R2ILOp::BoolOr { dst, a, b })
            }

            // Floating point comparison
            PcodeOp::FloatEqual => self.binary_op(raw, "FLOAT_EQUAL", |dst, a, b| {
                R2ILOp::FloatEqual { dst, a, b }
            }),
            PcodeOp::FloatNotEqual => self.binary_op(raw, "FLOAT_NOTEQUAL", |dst, a, b| {
                R2ILOp::FloatNotEqual { dst, a, b }
            }),
            PcodeOp::FloatLess => self.binary_op(raw, "FLOAT_LESS", |dst, a, b| {
                R2ILOp::FloatLess { dst, a, b }
            }),
            PcodeOp::FloatLessEqual => self.binary_op(raw, "FLOAT_LESSEQUAL", |dst, a, b| {
                R2ILOp::FloatLessEqual { dst, a, b }
            }),

            // Floating point operations
            PcodeOp::FloatNaN => {
                self.unary_op(raw, "FLOAT_NAN", |dst, src| R2ILOp::FloatNaN { dst, src })
            }
            PcodeOp::FloatAdd => {
                self.binary_op(raw, "FLOAT_ADD", |dst, a, b| R2ILOp::FloatAdd { dst, a, b })
            }
            PcodeOp::FloatSub => {
                self.binary_op(raw, "FLOAT_SUB", |dst, a, b| R2ILOp::FloatSub { dst, a, b })
            }
            PcodeOp::FloatMult => self.binary_op(raw, "FLOAT_MULT", |dst, a, b| {
                R2ILOp::FloatMult { dst, a, b }
            }),
            PcodeOp::FloatDiv => {
                self.binary_op(raw, "FLOAT_DIV", |dst, a, b| R2ILOp::FloatDiv { dst, a, b })
            }
            PcodeOp::FloatNeg => {
                self.unary_op(raw, "FLOAT_NEG", |dst, src| R2ILOp::FloatNeg { dst, src })
            }
            PcodeOp::FloatAbs => {
                self.unary_op(raw, "FLOAT_ABS", |dst, src| R2ILOp::FloatAbs { dst, src })
            }
            PcodeOp::FloatSqrt => {
                self.unary_op(raw, "FLOAT_SQRT", |dst, src| R2ILOp::FloatSqrt { dst, src })
            }
            PcodeOp::FloatCeil => {
                self.unary_op(raw, "FLOAT_CEIL", |dst, src| R2ILOp::FloatCeil { dst, src })
            }
            PcodeOp::FloatFloor => self.unary_op(raw, "FLOAT_FLOOR", |dst, src| {
                R2ILOp::FloatFloor { dst, src }
            }),
            PcodeOp::FloatRound => self.unary_op(raw, "FLOAT_ROUND", |dst, src| {
                R2ILOp::FloatRound { dst, src }
            }),

            // Conversions
            PcodeOp::Int2Float => {
                self.unary_op(raw, "INT2FLOAT", |dst, src| R2ILOp::Int2Float { dst, src })
            }
            PcodeOp::Float2Int => {
                self.unary_op(raw, "FLOAT2INT", |dst, src| R2ILOp::Float2Int { dst, src })
            }
            PcodeOp::FloatFloat => self.unary_op(raw, "FLOAT_FLOAT", |dst, src| {
                R2ILOp::FloatFloat { dst, src }
            }),
            PcodeOp::Trunc => self.unary_op(raw, "TRUNC", |dst, src| R2ILOp::Trunc { dst, src }),

            // Bit manipulation
            PcodeOp::Piece => {
                self.binary_op(raw, "PIECE", |dst, hi, lo| R2ILOp::Piece { dst, hi, lo })
            }
            PcodeOp::Subpiece => {
                translate::translate_subpiece(&self.wrap(raw)).map_err(translate_err)
            }
            PcodeOp::PopCount => {
                self.unary_op(raw, "POPCOUNT", |dst, src| R2ILOp::PopCount { dst, src })
            }
            PcodeOp::Lzcount => {
                self.unary_op(raw, "LZCOUNT", |dst, src| R2ILOp::Lzcount { dst, src })
            }

            // Analysis operations
            PcodeOp::Multiequal => {
                let dst = self.require_output(raw, "MULTIEQUAL")?;
                let inputs: Result<Vec<Varnode>> =
                    raw.inputs.iter().map(|v| self.convert_varnode(v)).collect();
                Ok(R2ILOp::Multiequal {
                    dst,
                    inputs: inputs?,
                })
            }

            PcodeOp::Indirect => {
                let dst = self.require_output(raw, "INDIRECT")?;
                let src = self.require_input(raw, 0, "INDIRECT")?;
                let indirect = self.require_input(raw, 1, "INDIRECT")?;
                Ok(R2ILOp::Indirect { dst, src, indirect })
            }

            PcodeOp::Cast => self.unary_op(raw, "CAST", |dst, src| R2ILOp::Cast { dst, src }),
            PcodeOp::New => self.unary_op(raw, "NEW", |dst, src| R2ILOp::New { dst, src }),
            PcodeOp::CpuId => {
                let dst = self.require_output(raw, "CPOOLREF")?;
                Ok(R2ILOp::CpuId { dst })
            }

            PcodeOp::PtrAdd => translate::translate_ptradd(&self.wrap(raw)).map_err(translate_err),

            PcodeOp::PtrSub => translate::translate_ptrsub(&self.wrap(raw)).map_err(translate_err),

            PcodeOp::SegmentOp => {
                let dst = self.require_output(raw, "SEGMENTOP")?;
                let segment = self.require_input(raw, 0, "SEGMENTOP")?;
                let offset = self.require_input(raw, 1, "SEGMENTOP")?;
                Ok(R2ILOp::SegmentOp {
                    dst,
                    segment,
                    offset,
                })
            }

            PcodeOp::Insert => {
                let dst = self.require_output(raw, "INSERT")?;
                let src = self.require_input(raw, 0, "INSERT")?;
                let value = self.require_input(raw, 1, "INSERT")?;
                let position = self.require_input(raw, 2, "INSERT")?;
                Ok(R2ILOp::Insert {
                    dst,
                    src,
                    value,
                    position,
                })
            }

            PcodeOp::Extract => {
                let dst = self.require_output(raw, "EXTRACT")?;
                let src = self.require_input(raw, 0, "EXTRACT")?;
                let position = self.require_input(raw, 1, "EXTRACT")?;
                Ok(R2ILOp::Extract { dst, src, position })
            }
        }
    }

    /// Helper for unary operations.
    fn unary_op<F>(&self, raw: &RawPcodeOp, name: &'static str, f: F) -> Result<R2ILOp>
    where
        F: FnOnce(Varnode, Varnode) -> R2ILOp,
    {
        translate::translate_unary(&self.wrap(raw), name, f).map_err(translate_err)
    }

    /// Helper for binary operations.
    fn binary_op<F>(&self, raw: &RawPcodeOp, name: &'static str, f: F) -> Result<R2ILOp>
    where
        F: FnOnce(Varnode, Varnode, Varnode) -> R2ILOp,
    {
        translate::translate_binary(&self.wrap(raw), name, f).map_err(translate_err)
    }

    /// Require an output varnode.
    fn require_output(&self, raw: &RawPcodeOp, name: &'static str) -> Result<Varnode> {
        raw.output
            .as_ref()
            .ok_or(PcodeError::MissingOutput(name))
            .and_then(|v| self.convert_varnode(v))
    }

    /// Require an input varnode at the given index.
    fn require_input(&self, raw: &RawPcodeOp, idx: usize, name: &'static str) -> Result<Varnode> {
        raw.inputs
            .get(idx)
            .ok_or(PcodeError::InvalidOperandCount {
                op: name,
                expected: idx + 1,
                got: raw.inputs.len(),
            })
            .and_then(|v| self.convert_varnode(v))
    }

    /// Require a raw input varnode at the given index (for constants like space IDs).
    fn require_raw_input<'a>(
        &self,
        raw: &'a RawPcodeOp,
        idx: usize,
        name: &'static str,
    ) -> Result<&'a RawVarnode> {
        raw.inputs.get(idx).ok_or(PcodeError::InvalidOperandCount {
            op: name,
            expected: idx + 1,
            got: raw.inputs.len(),
        })
    }
}

/// Helper to convert translation errors.
fn translate_err(e: translate::TranslateError) -> PcodeError {
    match e {
        translate::TranslateError::MissingOutput(op) => PcodeError::MissingOutput(op),
        translate::TranslateError::MissingInput(op, expected) => PcodeError::InvalidOperandCount {
            op,
            expected: expected + 1,
            got: 0, // We don't have the actual count easily available here
        },
        translate::TranslateError::InvalidSpace(idx) => PcodeError::InvalidSpace(idx),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_copy_translation() {
        let translator = PcodeTranslator::default_spaces();

        let raw = RawPcodeOp {
            opcode: PcodeOp::Copy as u32,
            output: Some(RawVarnode::new(2, 0, 8)), // register:0
            inputs: vec![RawVarnode::new(0, 42, 8)], // const:42
        };

        let result = translator.translate(&raw).unwrap();

        match result {
            R2ILOp::Copy { dst, src } => {
                assert!(dst.is_register());
                assert_eq!(dst.offset, 0);
                assert!(src.is_const());
                assert_eq!(src.offset, 42);
            }
            _ => panic!("Expected Copy operation"),
        }
    }

    #[test]
    fn test_add_translation() {
        let translator = PcodeTranslator::default_spaces();

        let raw = RawPcodeOp {
            opcode: PcodeOp::IntAdd as u32,
            output: Some(RawVarnode::new(2, 0, 4)), // register:0
            inputs: vec![
                RawVarnode::new(2, 0, 4), // register:0
                RawVarnode::new(0, 1, 4), // const:1
            ],
        };

        let result = translator.translate(&raw).unwrap();

        match result {
            R2ILOp::IntAdd { dst, a, b } => {
                assert!(dst.is_register());
                assert!(a.is_register());
                assert!(b.is_const());
                assert_eq!(b.offset, 1);
            }
            _ => panic!("Expected IntAdd operation"),
        }
    }
}
