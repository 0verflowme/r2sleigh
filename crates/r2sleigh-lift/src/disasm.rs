//! Disassembly and P-code lifting using libsla.
//!
//! This module provides runtime disassembly of instruction bytes to P-code
//! and translation to r2il using Ghidra's libsla library.

use libsla::{
    Address, AddressSpace, AddressSpaceType, BoolOp, FloatOp, GhidraSleigh, InstructionLoader,
    IntOp, IntSign, OpCode, PcodeDisassembly, PcodeInstruction, PseudoOp, Sleigh, VarnodeData,
};
use r2il::{
    AtomicKind, MemoryClass, MemoryOrdering, MemoryPermissions, OpMetadata, PointerHint, R2ILBlock,
    R2ILOp, ScalarKind, SpaceId, StorageClass, Varnode, select_register_name,
};
use std::collections::HashMap;

use crate::translate::{self, PcodeSource};
use crate::userops::{ARM64_PAUTH_AUTH_USEROP, ARM64_PAUTH_SIGN_USEROP, ARM64_PAUTH_STRIP_USEROP};
use crate::{LiftError, Result};

/// A disassembler that uses libsla to lift instructions to r2il.
pub struct Disassembler {
    /// The underlying Ghidra Sleigh instance
    sleigh: GhidraSleigh,
    /// Architecture name
    arch_name: String,
    /// Canonical register names by (offset, size)
    reg_name_map: HashMap<(u64, u32), String>,
    /// User-defined operations by index
    userop_map: HashMap<u32, String>,
}

/// Precision profile for lift-time semantic metadata inference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SemanticMetadataPrecision {
    /// Conservative high-confidence rules only.
    #[default]
    High,
}

/// Options that control semantic metadata generation during lifting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SemanticMetadataOptions {
    /// Enable or disable semantic metadata inference.
    pub enabled: bool,
    /// Inference profile. Phase 1 supports only high precision.
    pub precision: SemanticMetadataPrecision,
}

impl Default for SemanticMetadataOptions {
    fn default() -> Self {
        Self {
            enabled: true,
            precision: SemanticMetadataPrecision::High,
        }
    }
}

/// Wrapper for libsla PcodeInstruction that implements PcodeSource.
struct DisasmInstructionWrapper<'a> {
    instr: &'a PcodeInstruction,
    disasm: &'a Disassembler,
}

impl<'a> PcodeSource for DisasmInstructionWrapper<'a> {
    fn output(&self) -> Option<Varnode> {
        self.instr
            .output
            .as_ref()
            .map(|v| self.disasm.translate_varnode(v))
    }

    fn input(&self, idx: usize) -> Option<Varnode> {
        self.instr
            .inputs
            .get(idx)
            .map(|v| self.disasm.translate_varnode(v))
    }

    fn input_raw_offset(&self, idx: usize) -> Option<u64> {
        self.instr.inputs.get(idx).map(|v| v.address.offset)
    }

    fn input_count(&self) -> usize {
        self.instr.inputs.len()
    }

    fn space_from_index(&self, idx: u64) -> SpaceId {
        let spaces = self.disasm.sleigh.address_spaces();
        if let Some(space) = spaces.get(idx as usize) {
            self.disasm.translate_space(space)
        } else {
            SpaceId::Custom(idx as u32)
        }
    }
}

fn translate_err(e: translate::TranslateError) -> LiftError {
    match e {
        translate::TranslateError::MissingOutput(op) => {
            LiftError::Parse(format!("{} requires output", op))
        }
        translate::TranslateError::MissingInput(op, idx) => {
            LiftError::Parse(format!("{} requires input at index {}", op, idx))
        }
        translate::TranslateError::InvalidSpace(idx) => {
            LiftError::Parse(format!("Invalid space index: {}", idx))
        }
    }
}

fn build_register_name_map(sleigh: &GhidraSleigh) -> HashMap<(u64, u32), String> {
    let mut candidates: HashMap<(u64, u32), Vec<String>> = HashMap::new();

    for (varnode, name) in sleigh.register_name_map() {
        let key = (varnode.address.offset, varnode.size as u32);
        candidates.entry(key).or_default().push(name);
    }

    let mut map = HashMap::new();
    for (key, names) in candidates {
        if let Some(name) = select_register_name(names.iter().map(String::as_str)) {
            map.insert(key, name);
        }
    }

    map
}

impl Disassembler {
    /// Create a new disassembler from a precompiled .sla file and processor specification.
    ///
    /// # Arguments
    ///
    /// * `sla_bytes` - The compiled .sla file contents
    /// * `pspec` - The processor specification XML string
    /// * `arch_name` - Name of the architecture
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use r2sleigh_lift::disasm::Disassembler;
    ///
    /// // Using sleigh-config precompiled data
    /// let disasm = Disassembler::from_sla(
    ///     include_bytes!("x86-64.sla"),
    ///     include_str!("x86-64.pspec"),
    ///     "x86-64"
    /// )?;
    /// ```
    pub fn from_sla(sla_bytes: &[u8], pspec: &str, arch_name: &str) -> Result<Self> {
        let sleigh = GhidraSleigh::builder()
            .processor_spec(pspec)
            .map_err(|e| LiftError::Parse(format!("Invalid processor spec: {}", e)))?
            .build(sla_bytes)
            .map_err(|e| LiftError::Parse(format!("Failed to load .sla: {}", e)))?;

        let reg_name_map = build_register_name_map(&sleigh);

        Ok(Self {
            sleigh,
            arch_name: arch_name.to_string(),
            reg_name_map,
            userop_map: HashMap::new(),
        })
    }

    /// Get the architecture name.
    pub fn arch_name(&self) -> &str {
        &self.arch_name
    }

    /// Set user-defined operation names for CallOther resolution.
    pub fn set_userop_map(&mut self, map: HashMap<u32, String>) {
        self.userop_map = map;
    }

    /// Get the user-defined operation name for a CallOther index.
    pub fn userop_name(&self, index: u32) -> Option<&str> {
        self.userop_map.get(&index).map(String::as_str)
    }

    /// Get the default code address space.
    pub fn default_code_space(&self) -> AddressSpace {
        self.sleigh.default_code_space()
    }

    /// List all address spaces.
    pub fn address_spaces(&self) -> Vec<AddressSpace> {
        self.sleigh.address_spaces()
    }

    /// Get a register's varnode data by name.
    pub fn register(&self, name: &str) -> Result<VarnodeData> {
        self.sleigh
            .register_from_name(name)
            .map_err(|e| LiftError::Parse(format!("Unknown register '{}': {}", name, e)))
    }

    /// Get the register name for a varnode in the register space.
    ///
    /// Returns `None` if the varnode is not in the register space or if
    /// no register name is found for the given offset and size.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let vn = Varnode::register(0x20, 8); // RSP on x86-64
    /// let name = disasm.register_name(&vn);
    /// assert_eq!(name, Some("RSP".to_string()));
    /// ```
    pub fn register_name(&self, vn: &Varnode) -> Option<String> {
        if vn.space != SpaceId::Register {
            return None;
        }

        if let Some(name) = self.reg_name_map.get(&(vn.offset, vn.size)) {
            return Some(name.clone());
        }

        // Get the register address space
        let reg_space = self.sleigh.address_space_by_name("register")?;

        // Create a VarnodeData to query libsla
        let varnode_data = VarnodeData::new(Address::new(reg_space, vn.offset), vn.size as usize);

        self.sleigh.register_name(&varnode_data)
    }

    /// Format a varnode as a human-readable string, resolving register names.
    ///
    /// This is useful for pretty-printing P-code operations.
    pub fn format_varnode(&self, vn: &Varnode) -> String {
        match vn.space {
            SpaceId::Const => format!("0x{:x}", vn.offset),
            SpaceId::Register => {
                // Try to resolve the register name
                if let Some(name) = self.register_name(vn) {
                    name
                } else {
                    format!("reg:0x{:x}:{}", vn.offset, vn.size)
                }
            }
            SpaceId::Unique => format!("tmp:0x{:x}", vn.offset),
            SpaceId::Ram => format!("[0x{:x}]:{}", vn.offset, vn.size),
            SpaceId::Custom(n) => format!("space{}:0x{:x}", n, vn.offset),
        }
    }

    /// Disassemble instruction bytes at a given address and return r2il.
    ///
    /// # Arguments
    ///
    /// * `bytes` - Instruction bytes to disassemble
    /// * `addr` - Address where the instruction is located
    ///
    /// # Returns
    ///
    /// An `R2ILBlock` containing the translated operations, or an error.
    ///
    /// Note: This lifts a **single instruction**. Use `lift_block` to lift
    /// multiple instructions within a basic block.
    pub fn lift(&self, bytes: &[u8], addr: u64) -> Result<R2ILBlock> {
        self.lift_with_options(bytes, addr, SemanticMetadataOptions::default())
    }

    /// Lift a single instruction with explicit semantic metadata options.
    pub fn lift_with_options(
        &self,
        bytes: &[u8],
        addr: u64,
        options: SemanticMetadataOptions,
    ) -> Result<R2ILBlock> {
        let code_space = self.sleigh.default_code_space();
        let address = Address::new(code_space, addr);

        // Create an instruction loader from the bytes
        let loader = ByteLoader::new(bytes, addr);

        // Disassemble to P-code
        let pcode = self
            .sleigh
            .disassemble_pcode(&loader, address)
            .map_err(|e| {
                LiftError::Pcode(crate::pcode::PcodeError::InvalidOpcode(format!(
                    "Disassembly failed: {}",
                    e
                )))
            })?;

        // Translate P-code to r2il
        let mut block = self.translate_pcode(pcode, addr)?;
        let mnemonic = self
            .disasm_native(bytes, addr)
            .map(|(m, _)| m)
            .unwrap_or_default();
        self.normalize_memory_semantics(&mut block, &mnemonic);
        self.annotate_semantic_metadata(&mut block, options);
        Ok(block)
    }

    /// Minimum bytes required by libsla for disassembly.
    const MIN_BYTES: usize = 16;

    /// Lift an entire basic block (multiple instructions) to r2il.
    ///
    /// # Arguments
    ///
    /// * `bytes` - Instruction bytes for the entire block (should be at least 16 bytes for libsla)
    /// * `addr` - Starting address of the block
    /// * `block_size` - Size of the block in bytes
    ///
    /// # Returns
    ///
    /// An `R2ILBlock` containing operations from all instructions in the block.
    pub fn lift_block(&self, bytes: &[u8], addr: u64, block_size: usize) -> Result<R2ILBlock> {
        self.lift_block_with_options(bytes, addr, block_size, SemanticMetadataOptions::default())
    }

    /// Lift a basic block with explicit semantic metadata options.
    pub fn lift_block_with_options(
        &self,
        bytes: &[u8],
        addr: u64,
        block_size: usize,
        options: SemanticMetadataOptions,
    ) -> Result<R2ILBlock> {
        let mut combined_block = R2ILBlock::new(addr, block_size as u32);
        let mut offset = 0usize;

        while offset < block_size {
            let remaining = &bytes[offset..];
            if remaining.is_empty() {
                break;
            }

            let instr_addr = addr + offset as u64;

            // libsla requires at least 16 bytes; pad if necessary
            let lift_bytes: Vec<u8> = if remaining.len() < Self::MIN_BYTES {
                let mut padded = remaining.to_vec();
                padded.resize(Self::MIN_BYTES, 0);
                padded
            } else {
                remaining.to_vec()
            };

            // Lift single instruction
            match self.lift_with_options(&lift_bytes, instr_addr, options) {
                Ok(instr_block) => {
                    let R2ILBlock {
                        size: instr_size_u32,
                        ops,
                        op_metadata,
                        ..
                    } = instr_block;
                    let instr_size = instr_size_u32 as usize;
                    if instr_size == 0 {
                        // Prevent infinite loop on zero-size instruction
                        break;
                    }

                    let base_op_index = combined_block.ops.len();
                    let mut instr_op_metadata = op_metadata;
                    // Append all ops from this instruction
                    for op in ops {
                        combined_block.push(op);
                    }
                    for local_idx in 0..(combined_block.ops.len() - base_op_index) {
                        let mut meta = instr_op_metadata.remove(&local_idx).unwrap_or_default();
                        meta.instruction_addr = Some(instr_addr);
                        combined_block.set_op_metadata(base_op_index + local_idx, meta);
                    }

                    offset += instr_size;
                }
                Err(_) => {
                    // Stop on disassembly error (e.g., invalid instruction)
                    break;
                }
            }
        }

        // Update the block size to reflect actual bytes consumed
        combined_block.size = offset as u32;

        Ok(combined_block)
    }

    /// Disassemble and get native assembly mnemonic.
    pub fn disasm_native(&self, bytes: &[u8], addr: u64) -> Result<(String, usize)> {
        let code_space = self.sleigh.default_code_space();
        let address = Address::new(code_space, addr);
        let loader = ByteLoader::new(bytes, addr);

        let native = self
            .sleigh
            .disassemble_native(&loader, address)
            .map_err(|e| LiftError::Parse(format!("Disassembly failed: {}", e)))?;

        let mnemonic = format!(
            "{} {}",
            native.instruction.mnemonic, native.instruction.body
        );
        let size = native.origin.size;

        Ok((mnemonic.trim().to_string(), size))
    }

    /// Translate a P-code disassembly to an r2il block.
    fn translate_pcode(&self, pcode: PcodeDisassembly, addr: u64) -> Result<R2ILBlock> {
        let instr_size = pcode.origin.size as u32;
        let mut block = R2ILBlock::new(addr, instr_size);

        for pcode_instr in pcode.instructions {
            if let Some(op) = self.translate_pcode_op(&pcode_instr)? {
                block.push(op);
            }
        }

        Ok(block)
    }

    fn normalize_memory_semantics(&self, block: &mut R2ILBlock, mnemonic: &str) {
        normalize_memory_semantics_with_hints(
            block,
            &self.arch_name,
            mnemonic,
            |idx| self.userop_name(idx).map(str::to_string),
            |name| {
                self.register(name)
                    .ok()
                    .map(|vn| self.translate_varnode(&vn))
            },
        );
    }

    fn annotate_semantic_metadata(&self, block: &mut R2ILBlock, options: SemanticMetadataOptions) {
        annotate_semantic_metadata_with_hints(block, &self.arch_name, options, |vn| {
            self.register_name(vn)
        });
    }

    /// Translate a single P-code instruction to an r2il operation.
    fn translate_pcode_op(&self, instr: &PcodeInstruction) -> Result<Option<R2ILOp>> {
        let source = DisasmInstructionWrapper {
            instr,
            disasm: self,
        };

        // Helpers for common patterns
        let unary = |name, f: fn(Varnode, Varnode) -> R2ILOp| {
            translate::translate_unary(&source, name, f)
                .map(Some)
                .map_err(translate_err)
        };

        let binary = |name, f: fn(Varnode, Varnode, Varnode) -> R2ILOp| {
            translate::translate_binary(&source, name, f)
                .map(Some)
                .map_err(translate_err)
        };

        match &instr.op_code {
            // Data movement
            OpCode::Copy => unary("COPY", |dst, src| R2ILOp::Copy { dst, src }),

            OpCode::Load => translate::translate_load(&source)
                .map(Some)
                .map_err(translate_err),

            OpCode::Store => translate::translate_store(&source)
                .map(Some)
                .map_err(translate_err),

            // Control flow
            OpCode::Branch => {
                let target =
                    translate::require_input(&source, 0, "BRANCH").map_err(translate_err)?;
                Ok(Some(R2ILOp::Branch { target }))
            }

            OpCode::BranchConditional => translate::translate_cbranch(&source)
                .map(Some)
                .map_err(translate_err),

            OpCode::BranchIndirect => {
                let target =
                    translate::require_input(&source, 0, "BRANCHIND").map_err(translate_err)?;
                Ok(Some(R2ILOp::BranchInd { target }))
            }

            OpCode::Call => {
                let target = translate::require_input(&source, 0, "CALL").map_err(translate_err)?;
                Ok(Some(R2ILOp::Call { target }))
            }

            OpCode::CallIndirect => {
                let target =
                    translate::require_input(&source, 0, "CALLIND").map_err(translate_err)?;
                Ok(Some(R2ILOp::CallInd { target }))
            }

            OpCode::Return => {
                let target =
                    translate::require_input(&source, 0, "RETURN").map_err(translate_err)?;
                Ok(Some(R2ILOp::Return { target }))
            }

            // Integer arithmetic
            // Integer arithmetic
            OpCode::Int(IntOp::Add) => binary("INT_ADD", |dst, a, b| R2ILOp::IntAdd { dst, a, b }),
            OpCode::Int(IntOp::Subtract) => {
                binary("INT_SUB", |dst, a, b| R2ILOp::IntSub { dst, a, b })
            }
            OpCode::Int(IntOp::Multiply) => {
                binary("INT_MULT", |dst, a, b| R2ILOp::IntMult { dst, a, b })
            }
            OpCode::Int(IntOp::Divide(IntSign::Unsigned)) => {
                binary("INT_DIV", |dst, a, b| R2ILOp::IntDiv { dst, a, b })
            }
            OpCode::Int(IntOp::Divide(IntSign::Signed)) => {
                binary("INT_SDIV", |dst, a, b| R2ILOp::IntSDiv { dst, a, b })
            }
            OpCode::Int(IntOp::Remainder(IntSign::Unsigned)) => {
                binary("INT_REM", |dst, a, b| R2ILOp::IntRem { dst, a, b })
            }
            OpCode::Int(IntOp::Remainder(IntSign::Signed)) => {
                binary("INT_SREM", |dst, a, b| R2ILOp::IntSRem { dst, a, b })
            }
            OpCode::Int(IntOp::Negate) => {
                unary("INT_2COMP", |dst, src| R2ILOp::IntNegate { dst, src })
            }

            // Bitwise operations
            OpCode::Int(IntOp::Bitwise(BoolOp::And)) => {
                binary("INT_AND", |dst, a, b| R2ILOp::IntAnd { dst, a, b })
            }
            OpCode::Int(IntOp::Bitwise(BoolOp::Or)) => {
                binary("INT_OR", |dst, a, b| R2ILOp::IntOr { dst, a, b })
            }
            OpCode::Int(IntOp::Bitwise(BoolOp::Xor)) => {
                binary("INT_XOR", |dst, a, b| R2ILOp::IntXor { dst, a, b })
            }
            OpCode::Int(IntOp::Bitwise(BoolOp::Negate)) => {
                unary("INT_NEGATE", |dst, src| R2ILOp::IntNot { dst, src })
            }

            // Shift operations
            OpCode::Int(IntOp::ShiftLeft) => {
                binary("INT_LEFT", |dst, a, b| R2ILOp::IntLeft { dst, a, b })
            }
            OpCode::Int(IntOp::ShiftRight(IntSign::Unsigned)) => {
                binary("INT_RIGHT", |dst, a, b| R2ILOp::IntRight { dst, a, b })
            }
            OpCode::Int(IntOp::ShiftRight(IntSign::Signed)) => {
                binary("INT_SRIGHT", |dst, a, b| R2ILOp::IntSRight { dst, a, b })
            }

            // Comparison operations
            OpCode::Int(IntOp::Equal) => {
                binary("INT_EQUAL", |dst, a, b| R2ILOp::IntEqual { dst, a, b })
            }
            OpCode::Int(IntOp::NotEqual) => binary("INT_NOTEQUAL", |dst, a, b| {
                R2ILOp::IntNotEqual { dst, a, b }
            }),
            OpCode::Int(IntOp::LessThan(IntSign::Unsigned)) => {
                binary("INT_LESS", |dst, a, b| R2ILOp::IntLess { dst, a, b })
            }
            OpCode::Int(IntOp::LessThan(IntSign::Signed)) => {
                binary("INT_SLESS", |dst, a, b| R2ILOp::IntSLess { dst, a, b })
            }

            OpCode::Int(IntOp::LessThanOrEqual(IntSign::Unsigned)) => {
                binary("INT_LESSEQUAL", |dst, a, b| R2ILOp::IntLessEqual {
                    dst,
                    a,
                    b,
                })
            }

            OpCode::Int(IntOp::LessThanOrEqual(IntSign::Signed)) => {
                binary("INT_SLESSEQUAL", |dst, a, b| R2ILOp::IntSLessEqual {
                    dst,
                    a,
                    b,
                })
            }

            // Extension operations
            OpCode::Int(IntOp::Extension(IntSign::Unsigned)) => {
                unary("INT_ZEXT", |dst, src| R2ILOp::IntZExt { dst, src })
            }

            OpCode::Int(IntOp::Extension(IntSign::Signed)) => {
                unary("INT_SEXT", |dst, src| R2ILOp::IntSExt { dst, src })
            }

            // Carry/Borrow
            OpCode::Int(IntOp::Carry(IntSign::Unsigned)) => {
                binary("INT_CARRY", |dst, a, b| R2ILOp::IntCarry { dst, a, b })
            }

            OpCode::Int(IntOp::Carry(IntSign::Signed)) => {
                binary("INT_SCARRY", |dst, a, b| R2ILOp::IntSCarry { dst, a, b })
            }

            OpCode::Int(IntOp::Borrow) => {
                binary("INT_SBORROW", |dst, a, b| R2ILOp::IntSBorrow { dst, a, b })
            }

            // Boolean operations
            OpCode::Bool(BoolOp::And) => {
                binary("BOOL_AND", |dst, a, b| R2ILOp::BoolAnd { dst, a, b })
            }

            OpCode::Bool(BoolOp::Or) => binary("BOOL_OR", |dst, a, b| R2ILOp::BoolOr { dst, a, b }),

            OpCode::Bool(BoolOp::Xor) => {
                binary("BOOL_XOR", |dst, a, b| R2ILOp::BoolXor { dst, a, b })
            }

            OpCode::Bool(BoolOp::Negate) => {
                unary("BOOL_NEGATE", |dst, src| R2ILOp::BoolNot { dst, src })
            }

            // Piece/Subpiece
            // Piece/Subpiece
            OpCode::Piece => binary("PIECE", |dst, hi, lo| R2ILOp::Piece { dst, hi, lo }),

            OpCode::Subpiece => translate::translate_subpiece(&source)
                .map(Some)
                .map_err(translate_err),

            // Popcount/LzCount
            OpCode::Popcount => unary("POPCOUNT", |dst, src| R2ILOp::PopCount { dst, src }),

            OpCode::LzCount => unary("LZCOUNT", |dst, src| R2ILOp::Lzcount { dst, src }),

            // Floating point operations
            OpCode::Float(FloatOp::Add) => {
                binary("FLOAT_ADD", |dst, a, b| R2ILOp::FloatAdd { dst, a, b })
            }

            OpCode::Float(FloatOp::Subtract) => {
                binary("FLOAT_SUB", |dst, a, b| R2ILOp::FloatSub { dst, a, b })
            }

            OpCode::Float(FloatOp::Multiply) => {
                binary("FLOAT_MULT", |dst, a, b| R2ILOp::FloatMult { dst, a, b })
            }

            OpCode::Float(FloatOp::Divide) => {
                binary("FLOAT_DIV", |dst, a, b| R2ILOp::FloatDiv { dst, a, b })
            }

            OpCode::Float(FloatOp::Negate) => {
                unary("FLOAT_NEG", |dst, src| R2ILOp::FloatNeg { dst, src })
            }

            OpCode::Float(FloatOp::AbsoluteValue) => {
                unary("FLOAT_ABS", |dst, src| R2ILOp::FloatAbs { dst, src })
            }

            OpCode::Float(FloatOp::SquareRoot) => {
                unary("FLOAT_SQRT", |dst, src| R2ILOp::FloatSqrt { dst, src })
            }

            OpCode::Float(FloatOp::Equal) => {
                binary("FLOAT_EQUAL", |dst, a, b| R2ILOp::FloatEqual { dst, a, b })
            }

            OpCode::Float(FloatOp::NotEqual) => binary("FLOAT_NOTEQUAL", |dst, a, b| {
                R2ILOp::FloatNotEqual { dst, a, b }
            }),

            OpCode::Float(FloatOp::LessThan) => {
                binary("FLOAT_LESS", |dst, a, b| R2ILOp::FloatLess { dst, a, b })
            }

            OpCode::Float(FloatOp::LessThanOrEqual) => binary("FLOAT_LESSEQUAL", |dst, a, b| {
                R2ILOp::FloatLessEqual { dst, a, b }
            }),

            OpCode::Float(FloatOp::IsNaN) => {
                unary("FLOAT_NAN", |dst, src| R2ILOp::FloatNaN { dst, src })
            }

            OpCode::Float(FloatOp::IntToFloat) => {
                unary("INT2FLOAT", |dst, src| R2ILOp::Int2Float { dst, src })
            }

            OpCode::Float(FloatOp::FloatToFloat) => {
                unary("FLOAT_FLOAT", |dst, src| R2ILOp::FloatFloat { dst, src })
            }

            OpCode::Float(FloatOp::Truncate) => {
                unary("TRUNC", |dst, src| R2ILOp::Trunc { dst, src })
            }

            OpCode::Float(FloatOp::Ceiling) => {
                unary("FLOAT_CEIL", |dst, src| R2ILOp::FloatCeil { dst, src })
            }

            OpCode::Float(FloatOp::Floor) => {
                unary("FLOAT_FLOOR", |dst, src| R2ILOp::FloatFloor { dst, src })
            }

            OpCode::Float(FloatOp::Round) => {
                unary("FLOAT_ROUND", |dst, src| R2ILOp::FloatRound { dst, src })
            }

            // Pseudo operations
            OpCode::Pseudo(PseudoOp::CallOther) => {
                // CALLOTHER: first input is userop index, rest are arguments
                let userop_vn =
                    translate::require_input(&source, 0, "CALLOTHER").map_err(translate_err)?;
                let userop = userop_vn.offset as u32;
                let output = source.output();

                // Collect remaining inputs (args)
                let mut inputs = Vec::new();
                for i in 1..source.input_count() {
                    if let Some(input) = source.input(i) {
                        inputs.push(input);
                    }
                }

                Ok(Some(R2ILOp::CallOther {
                    userop,
                    output,
                    inputs,
                }))
            }

            // Analysis ops and unknowns - emit as Nop or unsupported marker
            OpCode::Analysis(_) | OpCode::Pseudo(_) | OpCode::Unknown(_) => {
                // Skip analysis-only operations
                Ok(None)
            }
        }
    }

    /// Convert a libsla VarnodeData to our Varnode type.
    fn translate_varnode(&self, vn: &VarnodeData) -> Varnode {
        let space = self.translate_space(&vn.address.address_space);
        Varnode {
            space,
            offset: vn.address.offset,
            size: vn.size as u32,
            meta: None,
        }
    }

    /// Convert a libsla AddressSpace to our SpaceId.
    fn translate_space(&self, space: &AddressSpace) -> SpaceId {
        match space.space_type {
            AddressSpaceType::Processor => {
                // Check if this is the register space
                if space.name.contains("register") || space.name == "register" {
                    SpaceId::Register
                } else {
                    SpaceId::Ram
                }
            }
            AddressSpaceType::Constant => SpaceId::Const,
            AddressSpaceType::Internal => SpaceId::Unique,
            _ => {
                // Use custom space with a hash of the name for unknown space types
                let hash = space
                    .name
                    .bytes()
                    .fold(0u32, |acc, b| acc.wrapping_add(b as u32));
                SpaceId::Custom(hash)
            }
        }
    }
}

/// Simple byte loader for instruction bytes.
struct ByteLoader<'a> {
    bytes: &'a [u8],
    base_addr: u64,
}

impl<'a> ByteLoader<'a> {
    fn new(bytes: &'a [u8], base_addr: u64) -> Self {
        Self { bytes, base_addr }
    }
}

impl<'a> InstructionLoader for ByteLoader<'a> {
    fn load_instruction_bytes(
        &self,
        varnode: &VarnodeData,
    ) -> std::result::Result<Vec<u8>, String> {
        let offset = varnode
            .address
            .offset
            .checked_sub(self.base_addr)
            .ok_or_else(|| "Address underflow".to_string())?;
        let start = offset as usize;
        let end = start
            .checked_add(varnode.size)
            .ok_or_else(|| "Size overflow".to_string())?;

        if end <= self.bytes.len() {
            Ok(self.bytes[start..end].to_vec())
        } else {
            Err(format!(
                "Out of bounds: requested {}..{}, have {}",
                start,
                end,
                self.bytes.len()
            ))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct VnKey {
    space: SpaceId,
    offset: u64,
    size: u32,
}

impl From<&Varnode> for VnKey {
    fn from(vn: &Varnode) -> Self {
        Self {
            space: vn.space,
            offset: vn.offset,
            size: vn.size,
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct InferredSemantics {
    storage_class: Option<StorageClass>,
    pointer_hint: Option<PointerHint>,
    scalar_kind: Option<ScalarKind>,
}

fn pointer_rank(hint: PointerHint) -> u8 {
    match hint {
        PointerHint::Unknown => 0,
        PointerHint::PointerLike => 1,
        PointerHint::CodePointer => 2,
    }
}

fn scalar_rank(kind: ScalarKind) -> u8 {
    match kind {
        ScalarKind::Unknown => 0,
        ScalarKind::Bitvector => 1,
        ScalarKind::Bool | ScalarKind::SignedInt | ScalarKind::UnsignedInt | ScalarKind::Float => 2,
    }
}

fn storage_rank(class: StorageClass) -> u8 {
    match class {
        StorageClass::Unknown => 0,
        StorageClass::Register => 1,
        StorageClass::Stack
        | StorageClass::Heap
        | StorageClass::Global
        | StorageClass::ThreadLocal
        | StorageClass::ConstData
        | StorageClass::Volatile => 2,
    }
}

fn memory_class_rank(class: MemoryClass) -> u8 {
    match class {
        MemoryClass::Unknown => 0,
        MemoryClass::Ram => 1,
        MemoryClass::Stack
        | MemoryClass::Heap
        | MemoryClass::Global
        | MemoryClass::ThreadLocal
        | MemoryClass::Mmio
        | MemoryClass::IoPort
        | MemoryClass::Code => 2,
    }
}

fn merge_inferred_field<T: Copy>(
    slot: &mut Option<T>,
    incoming: Option<T>,
    rank: impl Fn(T) -> u8,
) {
    let Some(new_val) = incoming else {
        return;
    };
    match slot {
        Some(old_val) if rank(*old_val) >= rank(new_val) => {}
        _ => {
            *slot = Some(new_val);
        }
    }
}

fn merge_inferred_semantics(dst: &mut InferredSemantics, src: InferredSemantics) {
    merge_inferred_field(&mut dst.storage_class, src.storage_class, storage_rank);
    merge_inferred_field(&mut dst.pointer_hint, src.pointer_hint, pointer_rank);
    merge_inferred_field(&mut dst.scalar_kind, src.scalar_kind, scalar_rank);
}

fn varnode_existing_inference(vn: &Varnode) -> InferredSemantics {
    let Some(meta) = vn.meta.as_ref() else {
        return InferredSemantics::default();
    };

    InferredSemantics {
        storage_class: meta
            .storage_class
            .filter(|v| !matches!(v, StorageClass::Unknown)),
        pointer_hint: meta
            .pointer_hint
            .filter(|v| !matches!(v, PointerHint::Unknown)),
        scalar_kind: meta
            .scalar_kind
            .filter(|v| !matches!(v, ScalarKind::Unknown)),
    }
}

fn update_inferred_semantics(
    inferred: &mut HashMap<VnKey, InferredSemantics>,
    vn: &Varnode,
    incoming: InferredSemantics,
) {
    let entry = inferred.entry(VnKey::from(vn)).or_default();
    merge_inferred_semantics(entry, incoming);
}

fn merged_varnode_inference(
    inferred: &HashMap<VnKey, InferredSemantics>,
    vn: &Varnode,
) -> InferredSemantics {
    let mut out = varnode_existing_inference(vn);
    if let Some(cur) = inferred.get(&VnKey::from(vn)) {
        merge_inferred_semantics(&mut out, *cur);
    }
    out
}

fn is_x86_arch(arch_name: &str) -> bool {
    arch_name.contains("x86")
}

fn is_stack_register(arch_name: &str, reg: &str) -> bool {
    if is_x86_arch(arch_name) {
        matches!(reg, "rsp" | "esp" | "sp" | "rbp" | "ebp" | "bp")
    } else {
        matches!(
            reg,
            "sp" | "rsp" | "esp" | "bp" | "rbp" | "ebp" | "fp" | "s0" | "x2" | "x8"
        )
    }
}

fn is_pc_register(reg: &str) -> bool {
    matches!(reg, "pc" | "rip" | "eip" | "ip")
}

fn is_x86_tls_register(arch_name: &str, reg: &str) -> bool {
    is_x86_arch(arch_name)
        && matches!(
            reg,
            "fs" | "gs" | "fsbase" | "gsbase" | "fs_base" | "gs_base"
        )
}

fn infer_address_storage_from_register(arch_name: &str, reg: &str) -> Option<StorageClass> {
    if is_x86_tls_register(arch_name, reg) {
        return Some(StorageClass::ThreadLocal);
    }
    if is_stack_register(arch_name, reg) {
        return Some(StorageClass::Stack);
    }
    if is_pc_register(reg) {
        return Some(StorageClass::Global);
    }
    None
}

fn map_storage_to_memory_class(storage: StorageClass) -> MemoryClass {
    match storage {
        StorageClass::Stack => MemoryClass::Stack,
        StorageClass::Heap => MemoryClass::Heap,
        StorageClass::Global => MemoryClass::Global,
        StorageClass::ThreadLocal => MemoryClass::ThreadLocal,
        StorageClass::Volatile => MemoryClass::Mmio,
        _ => MemoryClass::Ram,
    }
}

fn infer_op_memory_class(existing: Option<MemoryClass>, incoming: MemoryClass) -> MemoryClass {
    match existing {
        Some(cur) if memory_class_rank(cur) >= memory_class_rank(incoming) => cur,
        _ => incoming,
    }
}

fn infer_op_permissions(op: &R2ILOp, memory_class: MemoryClass) -> Option<MemoryPermissions> {
    let (read, write) = match op {
        R2ILOp::Load { .. } | R2ILOp::LoadLinked { .. } | R2ILOp::LoadGuarded { .. } => {
            (true, false)
        }
        R2ILOp::Store { .. } | R2ILOp::StoreConditional { .. } | R2ILOp::StoreGuarded { .. } => {
            (false, true)
        }
        R2ILOp::AtomicCAS { .. } => (true, true),
        _ => return None,
    };

    let (volatile, cacheable) = match memory_class {
        MemoryClass::Mmio | MemoryClass::IoPort => (true, false),
        _ => (false, true),
    };

    Some(MemoryPermissions {
        read,
        write,
        execute: matches!(memory_class, MemoryClass::Code),
        volatile,
        cacheable,
    })
}

fn apply_inferred_to_varnode(vn: &mut Varnode, inferred: &HashMap<VnKey, InferredSemantics>) {
    let Some(extra) = inferred.get(&VnKey::from(&*vn)).copied() else {
        return;
    };

    let mut meta = vn.meta.clone().unwrap_or_default();
    let mut changed = false;

    if let Some(storage) = extra.storage_class {
        match meta.storage_class {
            Some(cur) if storage_rank(cur) >= storage_rank(storage) => {}
            _ => {
                meta.storage_class = Some(storage);
                changed = true;
            }
        }
    }

    if let Some(hint) = extra.pointer_hint {
        match meta.pointer_hint {
            Some(cur) if pointer_rank(cur) >= pointer_rank(hint) => {}
            _ => {
                meta.pointer_hint = Some(hint);
                changed = true;
            }
        }
    }

    if let Some(kind) = extra.scalar_kind {
        match meta.scalar_kind {
            Some(cur) if scalar_rank(cur) >= scalar_rank(kind) => {}
            _ => {
                meta.scalar_kind = Some(kind);
                changed = true;
            }
        }
    }

    if changed {
        vn.meta = Some(meta);
    }
}

fn cached_register_name<F>(
    vn: &Varnode,
    reg_name_cache: &mut HashMap<VnKey, Option<String>>,
    resolve_register: &F,
) -> Option<String>
where
    F: Fn(&Varnode) -> Option<String>,
{
    if !vn.is_register() {
        return None;
    }

    let key = VnKey::from(vn);
    if let Some(cached) = reg_name_cache.get(&key) {
        return cached.clone();
    }

    let resolved = resolve_register(vn).map(|name| name.to_ascii_lowercase());
    reg_name_cache.insert(key, resolved.clone());
    resolved
}

fn inferred_address_storage<F>(
    vn: &Varnode,
    inferred: &HashMap<VnKey, InferredSemantics>,
    arch_name: &str,
    reg_name_cache: &mut HashMap<VnKey, Option<String>>,
    resolve_register: &F,
) -> Option<StorageClass>
where
    F: Fn(&Varnode) -> Option<String>,
{
    if let Some(info) = inferred.get(&VnKey::from(vn))
        && let Some(storage) = info.storage_class
        && !matches!(storage, StorageClass::Register | StorageClass::Unknown)
    {
        return Some(storage);
    }

    if let Some(name) = cached_register_name(vn, reg_name_cache, resolve_register) {
        return infer_address_storage_from_register(arch_name, &name);
    }

    None
}

fn annotate_semantic_metadata_with_hints<F>(
    block: &mut R2ILBlock,
    arch_name: &str,
    options: SemanticMetadataOptions,
    resolve_register: F,
) where
    F: Fn(&Varnode) -> Option<String>,
{
    if !options.enabled {
        return;
    }
    if !matches!(options.precision, SemanticMetadataPrecision::High) {
        return;
    }

    let arch = arch_name.to_ascii_lowercase();
    let mut inferred: HashMap<VnKey, InferredSemantics> = HashMap::new();
    let mut reg_name_cache: HashMap<VnKey, Option<String>> = HashMap::new();
    let mut op_memory_updates: Vec<(usize, MemoryClass, MemoryPermissions)> = Vec::new();

    for op in &block.ops {
        if let Some(dst) = op.output()
            && dst.is_register()
        {
            update_inferred_semantics(
                &mut inferred,
                dst,
                InferredSemantics {
                    storage_class: Some(StorageClass::Register),
                    ..Default::default()
                },
            );
        }
        for src in op.inputs() {
            if src.is_register() {
                update_inferred_semantics(
                    &mut inferred,
                    src,
                    InferredSemantics {
                        storage_class: Some(StorageClass::Register),
                        ..Default::default()
                    },
                );
            }
        }
    }

    for (op_index, op) in block.ops.iter().enumerate() {
        let mut dst_infer = InferredSemantics::default();
        match op {
            R2ILOp::Load { addr, .. }
            | R2ILOp::LoadLinked { addr, .. }
            | R2ILOp::LoadGuarded { addr, .. }
            | R2ILOp::Store { addr, .. }
            | R2ILOp::StoreConditional { addr, .. }
            | R2ILOp::StoreGuarded { addr, .. }
            | R2ILOp::AtomicCAS { addr, .. } => {
                update_inferred_semantics(
                    &mut inferred,
                    addr,
                    InferredSemantics {
                        pointer_hint: Some(PointerHint::PointerLike),
                        ..Default::default()
                    },
                );
                let addr_storage = inferred_address_storage(
                    addr,
                    &inferred,
                    &arch,
                    &mut reg_name_cache,
                    &resolve_register,
                );
                if let Some(storage) = addr_storage {
                    update_inferred_semantics(
                        &mut inferred,
                        addr,
                        InferredSemantics {
                            storage_class: Some(storage),
                            ..Default::default()
                        },
                    );
                }
                let memory_class =
                    map_storage_to_memory_class(addr_storage.unwrap_or(StorageClass::Unknown));
                if let Some(permissions) = infer_op_permissions(op, memory_class) {
                    op_memory_updates.push((op_index, memory_class, permissions));
                }
            }
            R2ILOp::CallInd { target } | R2ILOp::BranchInd { target } => {
                update_inferred_semantics(
                    &mut inferred,
                    target,
                    InferredSemantics {
                        pointer_hint: Some(PointerHint::CodePointer),
                        ..Default::default()
                    },
                );
            }
            R2ILOp::PtrAdd { base, .. } | R2ILOp::PtrSub { base, .. } => {
                dst_infer.pointer_hint = Some(PointerHint::PointerLike);
                dst_infer.storage_class = inferred_address_storage(
                    base,
                    &inferred,
                    &arch,
                    &mut reg_name_cache,
                    &resolve_register,
                );
            }
            R2ILOp::SegmentOp {
                segment, offset, ..
            } => {
                dst_infer.pointer_hint = Some(PointerHint::PointerLike);
                let seg_storage = inferred_address_storage(
                    segment,
                    &inferred,
                    &arch,
                    &mut reg_name_cache,
                    &resolve_register,
                );
                let off_storage = inferred_address_storage(
                    offset,
                    &inferred,
                    &arch,
                    &mut reg_name_cache,
                    &resolve_register,
                );
                dst_infer.storage_class = seg_storage.or(off_storage);
            }
            R2ILOp::Copy { src, .. } | R2ILOp::Cast { src, .. } | R2ILOp::New { src, .. } => {
                dst_infer = merged_varnode_inference(&inferred, src);
                if matches!(
                    dst_infer.storage_class,
                    None | Some(StorageClass::Unknown) | Some(StorageClass::Register)
                ) {
                    dst_infer.storage_class = inferred_address_storage(
                        src,
                        &inferred,
                        &arch,
                        &mut reg_name_cache,
                        &resolve_register,
                    )
                    .or(dst_infer.storage_class);
                }
            }
            R2ILOp::IntAdd { a, b, .. } | R2ILOp::IntSub { a, b, .. } => {
                let a_inf = merged_varnode_inference(&inferred, a);
                let b_inf = merged_varnode_inference(&inferred, b);
                let a_addr_storage = inferred_address_storage(
                    a,
                    &inferred,
                    &arch,
                    &mut reg_name_cache,
                    &resolve_register,
                );
                let b_addr_storage = inferred_address_storage(
                    b,
                    &inferred,
                    &arch,
                    &mut reg_name_cache,
                    &resolve_register,
                );
                let a_is_pointer = a_inf.pointer_hint.is_some() || a_addr_storage.is_some();
                let b_is_pointer = b_inf.pointer_hint.is_some() || b_addr_storage.is_some();
                if (a_is_pointer && b.is_const()) || (b_is_pointer && a.is_const()) {
                    dst_infer.pointer_hint = Some(PointerHint::PointerLike);
                    dst_infer.storage_class = if a_is_pointer {
                        a_addr_storage.or(a_inf.storage_class)
                    } else {
                        b_addr_storage.or(b_inf.storage_class)
                    };
                }
            }
            R2ILOp::BoolNot { .. }
            | R2ILOp::BoolAnd { .. }
            | R2ILOp::BoolOr { .. }
            | R2ILOp::BoolXor { .. }
            | R2ILOp::IntEqual { .. }
            | R2ILOp::IntNotEqual { .. }
            | R2ILOp::IntLess { .. }
            | R2ILOp::IntSLess { .. }
            | R2ILOp::IntLessEqual { .. }
            | R2ILOp::IntSLessEqual { .. }
            | R2ILOp::FloatEqual { .. }
            | R2ILOp::FloatNotEqual { .. }
            | R2ILOp::FloatLess { .. }
            | R2ILOp::FloatLessEqual { .. }
            | R2ILOp::FloatNaN { .. } => {
                dst_infer.scalar_kind = Some(ScalarKind::Bool);
            }
            R2ILOp::FloatAdd { .. }
            | R2ILOp::FloatSub { .. }
            | R2ILOp::FloatMult { .. }
            | R2ILOp::FloatDiv { .. }
            | R2ILOp::FloatNeg { .. }
            | R2ILOp::FloatAbs { .. }
            | R2ILOp::FloatSqrt { .. }
            | R2ILOp::FloatCeil { .. }
            | R2ILOp::FloatFloor { .. }
            | R2ILOp::FloatRound { .. }
            | R2ILOp::Int2Float { .. }
            | R2ILOp::FloatFloat { .. } => {
                dst_infer.scalar_kind = Some(ScalarKind::Float);
            }
            R2ILOp::IntSDiv { .. }
            | R2ILOp::IntSRem { .. }
            | R2ILOp::IntSRight { .. }
            | R2ILOp::IntSExt { .. }
            | R2ILOp::IntNegate { .. } => {
                dst_infer.scalar_kind = Some(ScalarKind::SignedInt);
            }
            R2ILOp::IntDiv { .. } | R2ILOp::IntRem { .. } | R2ILOp::IntZExt { .. } => {
                dst_infer.scalar_kind = Some(ScalarKind::UnsignedInt);
            }
            _ => {}
        }

        if let Some(dst) = op.output() {
            update_inferred_semantics(&mut inferred, dst, dst_infer);
        }
    }

    for (op_index, incoming_class, incoming_perms) in op_memory_updates {
        let current = block.op_metadata(op_index).and_then(|m| m.memory_class);
        let merged_class = infer_op_memory_class(current, incoming_class);
        let mut meta = block.op_metadata(op_index).cloned().unwrap_or_default();
        meta.memory_class = Some(merged_class);
        if meta.permissions.is_none() {
            meta.permissions = Some(incoming_perms);
        }
        block.set_op_metadata(op_index, meta);
    }

    for op in &mut block.ops {
        if let Some(dst) = op.output_mut() {
            apply_inferred_to_varnode(dst, &inferred);
        }
        for src in op.inputs_mut() {
            apply_inferred_to_varnode(src, &inferred);
        }
    }
}

fn normalize_memory_semantics_with_hints<F, G>(
    block: &mut R2ILBlock,
    arch_name: &str,
    mnemonic: &str,
    userop_name: F,
    resolve_register: G,
) where
    F: Fn(u32) -> Option<String>,
    G: Fn(&str) -> Option<Varnode>,
{
    let arch = arch_name.to_ascii_lowercase();
    let token = mnemonic
        .split_whitespace()
        .next()
        .unwrap_or_default()
        .to_ascii_lowercase();

    let mut replaced_fence_userop = false;
    for op_index in 0..block.ops.len() {
        let replacement = match &block.ops[op_index] {
            R2ILOp::CallOther {
                output,
                userop,
                inputs: _,
            } => {
                let name = userop_name(*userop).unwrap_or_default();
                if output.is_none() && is_fence_userop_name(&name) {
                    Some(R2ILOp::Fence {
                        ordering: MemoryOrdering::SeqCst,
                    })
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(new_op) = replacement {
            block.ops[op_index] = new_op;
            set_memory_hints(
                block,
                op_index,
                Some(AtomicKind::Fence),
                Some(MemoryOrdering::SeqCst),
            );
            replaced_fence_userop = true;
        }
    }

    if is_fence_mnemonic(&token)
        && !replaced_fence_userop
        && !block
            .ops
            .iter()
            .any(|op| matches!(op, R2ILOp::Fence { .. }))
    {
        let op_index = block.ops.len();
        block.push_with_metadata(
            R2ILOp::Fence {
                ordering: MemoryOrdering::SeqCst,
            },
            Some(OpMetadata {
                atomic_kind: Some(AtomicKind::Fence),
                memory_ordering: Some(MemoryOrdering::SeqCst),
                ..Default::default()
            }),
        );
        set_memory_hints(
            block,
            op_index,
            Some(AtomicKind::Fence),
            Some(MemoryOrdering::SeqCst),
        );
    }

    if block.ops.is_empty()
        && is_arm64_arch_name(&arch)
        && let Some(op) = pointer_auth_userop_from_mnemonic(&token, mnemonic, &resolve_register)
    {
        block.push_with_metadata(
            op,
            Some(OpMetadata {
                instruction_addr: Some(block.addr),
                ..Default::default()
            }),
        );
    }

    let op_ordering = ordering_from_mnemonic_token(&token);
    let lr_like = (arch.contains("riscv") && token.starts_with("lr."))
        || (arch.contains("arm") && token.starts_with("ldrex"));
    if lr_like
        && let Some((op_index, dst, space, addr)) =
            block.ops.iter().enumerate().find_map(|(i, op)| match op {
                R2ILOp::Load { dst, space, addr } if *space == SpaceId::Ram => {
                    Some((i, dst.clone(), *space, addr.clone()))
                }
                _ => None,
            })
    {
        block.ops[op_index] = R2ILOp::LoadLinked {
            dst,
            space,
            addr,
            ordering: op_ordering,
        };
        set_memory_hints(
            block,
            op_index,
            Some(AtomicKind::LoadLinked),
            Some(op_ordering),
        );
    }

    let sc_like = (arch.contains("riscv") && token.starts_with("sc."))
        || (arch.contains("arm") && token.starts_with("strex"));
    if sc_like
        && let Some((op_index, space, addr, val)) =
            block.ops.iter().enumerate().find_map(|(i, op)| match op {
                R2ILOp::Store { space, addr, val } if *space == SpaceId::Ram => {
                    Some((i, *space, addr.clone(), val.clone()))
                }
                _ => None,
            })
    {
        let result_candidate = storeconditional_result_from_mnemonic(mnemonic, &resolve_register)
            .or_else(|| nearest_register_output(block, op_index));
        block.ops[op_index] = R2ILOp::StoreConditional {
            result: result_candidate,
            space,
            addr,
            val,
            ordering: op_ordering,
        };
        set_memory_hints(
            block,
            op_index,
            Some(AtomicKind::StoreConditional),
            Some(op_ordering),
        );
    }

    if arch.contains("riscv") && token.starts_with("amo") {
        for op_index in 0..block.ops.len() {
            let is_memory = matches!(
                block.ops[op_index],
                R2ILOp::Load {
                    space: SpaceId::Ram,
                    ..
                } | R2ILOp::Store {
                    space: SpaceId::Ram,
                    ..
                } | R2ILOp::LoadLinked {
                    space: SpaceId::Ram,
                    ..
                } | R2ILOp::StoreConditional {
                    space: SpaceId::Ram,
                    ..
                } | R2ILOp::AtomicCAS {
                    space: SpaceId::Ram,
                    ..
                } | R2ILOp::LoadGuarded {
                    space: SpaceId::Ram,
                    ..
                } | R2ILOp::StoreGuarded {
                    space: SpaceId::Ram,
                    ..
                }
            );
            if is_memory {
                set_memory_hints(
                    block,
                    op_index,
                    Some(AtomicKind::ReadModifyWrite),
                    Some(op_ordering),
                );
            }
        }
    }
}

fn is_arm64_arch_name(arch: &str) -> bool {
    arch.contains("aarch64") || arch.contains("arm64")
}

fn pointer_auth_userop_for_token(token: &str) -> Option<u32> {
    if token.starts_with("aut") {
        Some(ARM64_PAUTH_AUTH_USEROP)
    } else if token.starts_with("xpac") {
        Some(ARM64_PAUTH_STRIP_USEROP)
    } else if token.starts_with("pac") {
        Some(ARM64_PAUTH_SIGN_USEROP)
    } else {
        None
    }
}

fn pointer_auth_operands(mnemonic: &str) -> Vec<&str> {
    mnemonic
        .split_once(char::is_whitespace)
        .map(|(_, operands)| operands)
        .unwrap_or_default()
        .split(',')
        .map(str::trim)
        .filter(|operand| !operand.is_empty())
        .collect()
}

fn pointer_auth_userop_from_mnemonic<G>(
    token: &str,
    mnemonic: &str,
    resolve_register: &G,
) -> Option<R2ILOp>
where
    G: Fn(&str) -> Option<Varnode>,
{
    let userop = pointer_auth_userop_for_token(token)?;
    let operands = pointer_auth_operands(mnemonic);
    let dst_name = operands.first().copied().or(match token {
        "pacibsp" | "paciasp" | "autibsp" | "autiasp" | "xpaclri" => Some("x30"),
        _ => None,
    })?;
    let dst = resolve_register(dst_name)?;
    let mut inputs = Vec::new();
    inputs.push(dst.clone());
    for operand in operands.iter().skip(1).copied() {
        if let Some(input) = resolve_register(operand) {
            inputs.push(input);
        }
    }
    if operands.len() <= 1
        && matches!(token, "pacibsp" | "paciasp" | "autibsp" | "autiasp")
        && let Some(sp) = resolve_register("sp")
    {
        inputs.push(sp);
    }
    Some(R2ILOp::CallOther {
        output: Some(dst),
        userop,
        inputs,
    })
}

fn set_memory_hints(
    block: &mut R2ILBlock,
    op_index: usize,
    atomic_kind: Option<AtomicKind>,
    ordering: Option<MemoryOrdering>,
) {
    let meta = block.op_metadata.entry(op_index).or_default();
    if let Some(kind) = atomic_kind {
        meta.atomic_kind = Some(kind);
    }
    if let Some(ord) = ordering {
        meta.memory_ordering = Some(ord);
    }
}

fn nearest_register_output(block: &R2ILBlock, pivot_index: usize) -> Option<Varnode> {
    if pivot_index > 0
        && let Some(vn) = block.ops[..pivot_index]
            .iter()
            .rev()
            .filter_map(R2ILOp::output)
            .find(|vn| vn.space == SpaceId::Register && vn.size > 0)
    {
        return Some(vn.clone());
    }

    block
        .ops
        .iter()
        .skip(pivot_index.saturating_add(1))
        .filter_map(R2ILOp::output)
        .find(|vn| vn.space == SpaceId::Register && vn.size > 0)
        .cloned()
}

fn storeconditional_result_from_mnemonic<G>(mnemonic: &str, resolve_register: G) -> Option<Varnode>
where
    G: Fn(&str) -> Option<Varnode>,
{
    let mut parts = mnemonic.trim().splitn(2, char::is_whitespace);
    let _op = parts.next()?;
    let operands = parts.next()?.trim();
    if operands.is_empty() {
        return None;
    }

    let first_operand = operands.split(',').next()?.trim();
    let reg_name = first_operand.trim_matches(|c| matches!(c, '[' | ']' | '(' | ')' | '{' | '}'));
    if reg_name.is_empty() {
        return None;
    }
    resolve_register(reg_name)
}

fn is_fence_userop_name(name: &str) -> bool {
    let normalized = name.trim().to_ascii_lowercase();
    matches!(
        normalized.as_str(),
        "fence"
            | "fence.i"
            | "sfence.vm"
            | "sfence.vma"
            | "datamemorybarrier"
            | "datasynchronizationbarrier"
            | "instructionsynchronizationbarrier"
    )
}

fn is_fence_mnemonic(token: &str) -> bool {
    let token = token.trim().to_ascii_lowercase();
    token == "fence"
        || token == "fence.i"
        || token == "sfence.vm"
        || token == "sfence.vma"
        || token.starts_with("dmb")
        || token.starts_with("dsb")
        || token.starts_with("isb")
}

fn ordering_from_mnemonic_token(token: &str) -> MemoryOrdering {
    let t = token.to_ascii_lowercase();
    let has_aq = t.contains(".aq");
    let has_rl = t.contains(".rl");
    if t.contains(".aqrl") || (has_aq && has_rl) {
        MemoryOrdering::AcqRel
    } else if has_aq {
        MemoryOrdering::Acquire
    } else if has_rl {
        MemoryOrdering::Release
    } else {
        MemoryOrdering::Relaxed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reg(offset: u64, size: u32) -> Varnode {
        Varnode::register(offset, size)
    }

    fn ram_addr(offset: u64, size: u32) -> Varnode {
        Varnode::new(SpaceId::Ram, offset, size)
    }

    fn arm64_reg(name: &str) -> Option<Varnode> {
        match name {
            "x16" => Some(reg(16 * 8, 8)),
            "x17" => Some(reg(17 * 8, 8)),
            "x30" | "lr" => Some(reg(30 * 8, 8)),
            "sp" => Some(reg(31 * 8, 8)),
            _ => None,
        }
    }

    #[test]
    fn normalization_fence_userop_rewrites_to_fence() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::CallOther {
            output: None,
            userop: 7,
            inputs: vec![],
        });

        normalize_memory_semantics_with_hints(
            &mut block,
            "riscv64",
            "addi x0, x0, 0",
            |idx| {
                if idx == 7 {
                    Some("fence".to_string())
                } else {
                    None
                }
            },
            |_| None,
        );

        assert!(matches!(block.ops[0], R2ILOp::Fence { .. }));
        let meta = block.op_metadata.get(&0).expect("metadata for op 0");
        assert_eq!(meta.atomic_kind, Some(AtomicKind::Fence));
        assert_eq!(meta.memory_ordering, Some(MemoryOrdering::SeqCst));
    }

    #[test]
    fn normalization_arm64_pointer_auth_register_form_becomes_named_userop() {
        let mut block = R2ILBlock::new(0x1000, 4);

        normalize_memory_semantics_with_hints(
            &mut block,
            "aarch64",
            "autda x16, x17",
            |_| None,
            arm64_reg,
        );

        match &block.ops[0] {
            R2ILOp::CallOther {
                output: Some(output),
                userop,
                inputs,
            } => {
                assert_eq!(*userop, ARM64_PAUTH_AUTH_USEROP);
                assert_eq!(*output, reg(16 * 8, 8));
                assert_eq!(inputs, &vec![reg(16 * 8, 8), reg(17 * 8, 8)]);
            }
            other => panic!("expected pointer-auth CallOther, got {other:?}"),
        }
    }

    #[test]
    fn normalization_arm64_pointer_auth_stack_form_preserves_lr_and_sp_evidence() {
        let mut block = R2ILBlock::new(0x2000, 4);

        normalize_memory_semantics_with_hints(&mut block, "arm64", "pacibsp", |_| None, arm64_reg);

        match &block.ops[0] {
            R2ILOp::CallOther {
                output: Some(output),
                userop,
                inputs,
            } => {
                assert_eq!(*userop, ARM64_PAUTH_SIGN_USEROP);
                assert_eq!(*output, reg(30 * 8, 8));
                assert_eq!(inputs, &vec![reg(30 * 8, 8), reg(31 * 8, 8)]);
            }
            other => panic!("expected stack pointer-auth CallOther, got {other:?}"),
        }
        assert_eq!(
            block.op_metadata(0).and_then(|meta| meta.instruction_addr),
            Some(0x2000)
        );
    }

    #[test]
    fn normalization_lr_rewrites_load_to_loadlinked() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Load {
            dst: reg(0, 8),
            space: SpaceId::Ram,
            addr: reg(8, 8),
        });

        normalize_memory_semantics_with_hints(
            &mut block,
            "riscv64",
            "lr.w.aq a0,(a1)",
            |_| None,
            |_| None,
        );

        match &block.ops[0] {
            R2ILOp::LoadLinked { ordering, .. } => {
                assert_eq!(*ordering, MemoryOrdering::Acquire);
            }
            other => panic!("expected LoadLinked, got {other:?}"),
        }
    }

    #[test]
    fn normalization_sc_rewrites_store_to_storeconditional() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: reg(0, 4),
            src: reg(4, 4),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: reg(8, 8),
            val: reg(12, 8),
        });

        normalize_memory_semantics_with_hints(
            &mut block,
            "riscv64",
            "sc.w.rl a0,a1,(a2)",
            |_| None,
            |name| {
                if name.eq_ignore_ascii_case("a0") {
                    Some(reg(32, 8))
                } else {
                    None
                }
            },
        );

        match &block.ops[1] {
            R2ILOp::StoreConditional {
                result, ordering, ..
            } => {
                assert_eq!(*ordering, MemoryOrdering::Release);
                assert_eq!(result.as_ref().map(|v| (v.offset, v.size)), Some((32, 8)));
            }
            other => panic!("expected StoreConditional, got {other:?}"),
        }
    }

    #[test]
    fn normalization_amo_adds_metadata() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Load {
            dst: reg(0, 8),
            space: SpaceId::Ram,
            addr: ram_addr(0x2000, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: ram_addr(0x2000, 8),
            val: reg(8, 8),
        });

        normalize_memory_semantics_with_hints(
            &mut block,
            "riscv64",
            "amoadd.w.aqrl a0,a1,(a2)",
            |_| None,
            |_| None,
        );

        for op_index in 0..2usize {
            let meta = block
                .op_metadata
                .get(&op_index)
                .expect("metadata for amo op");
            assert_eq!(meta.atomic_kind, Some(AtomicKind::ReadModifyWrite));
            assert_eq!(meta.memory_ordering, Some(MemoryOrdering::AcqRel));
        }
    }

    #[test]
    fn normalization_ambiguous_mnemonic_keeps_ops() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: reg(0, 8),
            val: reg(8, 8),
        });

        normalize_memory_semantics_with_hints(
            &mut block,
            "riscv64",
            "add x1,x2,x3",
            |_| None,
            |_| None,
        );

        assert!(matches!(block.ops[0], R2ILOp::Store { .. }));
    }

    #[test]
    fn normalization_sc_fallback_picks_nearest_register_output() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: reg(0, 8),
            src: reg(4, 8),
        });
        block.push(R2ILOp::Copy {
            dst: reg(16, 8),
            src: reg(20, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: reg(8, 8),
            val: reg(12, 8),
        });

        normalize_memory_semantics_with_hints(
            &mut block,
            "riscv64",
            "sc.w.rl unknown,a1,(a2)",
            |_| None,
            |_| None,
        );

        match &block.ops[2] {
            R2ILOp::StoreConditional { result, .. } => {
                assert_eq!(result.as_ref().map(|v| (v.offset, v.size)), Some((16, 8)));
            }
            other => panic!("expected StoreConditional, got {other:?}"),
        }
    }

    fn reg_name_resolver<'a>(
        map: &'a [(u64, u32, &'a str)],
    ) -> impl Fn(&Varnode) -> Option<String> + 'a {
        move |vn| {
            map.iter()
                .find(|(off, size, _)| *off == vn.offset && *size == vn.size)
                .map(|(_, _, name)| (*name).to_string())
        }
    }

    #[test]
    fn semantic_metadata_marks_pointer_and_stack_memory_class() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Load {
            dst: reg(0x10, 8),
            space: SpaceId::Ram,
            addr: reg(0x20, 8),
        });

        annotate_semantic_metadata_with_hints(
            &mut block,
            "x86-64",
            SemanticMetadataOptions::default(),
            reg_name_resolver(&[(0x10, 8, "rax"), (0x20, 8, "rsp")]),
        );

        let R2ILOp::Load { addr, .. } = &block.ops[0] else {
            panic!("expected load op");
        };
        let meta = addr.meta.as_ref().expect("address metadata");
        assert_eq!(meta.pointer_hint, Some(PointerHint::PointerLike));
        assert_eq!(meta.storage_class, Some(StorageClass::Stack));

        let op_meta = block.op_metadata(0).expect("load op metadata");
        assert_eq!(op_meta.memory_class, Some(MemoryClass::Stack));
        assert_eq!(
            op_meta.permissions,
            Some(MemoryPermissions {
                read: true,
                write: false,
                execute: false,
                volatile: false,
                cacheable: true,
            })
        );
    }

    #[test]
    fn semantic_metadata_marks_indirect_targets_as_code_pointers() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::CallInd {
            target: reg(0x30, 8),
        });

        annotate_semantic_metadata_with_hints(
            &mut block,
            "x86-64",
            SemanticMetadataOptions::default(),
            reg_name_resolver(&[(0x30, 8, "rax")]),
        );

        let R2ILOp::CallInd { target } = &block.ops[0] else {
            panic!("expected callind op");
        };
        let meta = target.meta.as_ref().expect("target metadata");
        assert_eq!(meta.pointer_hint, Some(PointerHint::CodePointer));
    }

    #[test]
    fn semantic_metadata_classifies_global_and_tls_memory() {
        let mut block = R2ILBlock::new(0x1000, 8);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x100, 8),
            a: reg(0x40, 8),
            b: Varnode::constant(0x20, 8),
        });
        block.push(R2ILOp::Load {
            dst: reg(0x48, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x100, 8),
        });
        block.push(R2ILOp::Load {
            dst: reg(0x50, 8),
            space: SpaceId::Ram,
            addr: reg(0x60, 8),
        });

        annotate_semantic_metadata_with_hints(
            &mut block,
            "x86-64",
            SemanticMetadataOptions::default(),
            reg_name_resolver(&[
                (0x40, 8, "rip"),
                (0x48, 8, "rax"),
                (0x50, 8, "rbx"),
                (0x60, 8, "fs"),
            ]),
        );

        let R2ILOp::IntAdd { dst, .. } = &block.ops[0] else {
            panic!("expected intadd");
        };
        let dst_meta = dst.meta.as_ref().expect("tmp metadata");
        assert_eq!(dst_meta.storage_class, Some(StorageClass::Global));
        assert_eq!(dst_meta.pointer_hint, Some(PointerHint::PointerLike));

        let op_meta_global = block.op_metadata(1).expect("global load metadata");
        assert_eq!(op_meta_global.memory_class, Some(MemoryClass::Global));

        let op_meta_tls = block.op_metadata(2).expect("tls load metadata");
        assert_eq!(op_meta_tls.memory_class, Some(MemoryClass::ThreadLocal));
        assert_eq!(
            op_meta_tls.permissions,
            Some(MemoryPermissions {
                read: true,
                write: false,
                execute: false,
                volatile: false,
                cacheable: true,
            })
        );
    }

    #[test]
    fn semantic_metadata_generic_stack_fallback() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: reg(0x200, 8),
            val: reg(0x208, 8),
        });

        annotate_semantic_metadata_with_hints(
            &mut block,
            "riscv64",
            SemanticMetadataOptions::default(),
            reg_name_resolver(&[(0x200, 8, "sp"), (0x208, 8, "a0")]),
        );

        let op_meta = block.op_metadata(0).expect("store metadata");
        assert_eq!(op_meta.memory_class, Some(MemoryClass::Stack));
        assert_eq!(
            op_meta.permissions,
            Some(MemoryPermissions {
                read: false,
                write: true,
                execute: false,
                volatile: false,
                cacheable: true,
            })
        );
    }

    #[test]
    fn semantic_metadata_marks_mmio_permissions_as_volatile_non_cacheable() {
        let mut block = R2ILBlock::new(0x1000, 4);
        let mut src = reg(0x20, 8);
        src.meta = Some(r2il::VarnodeMetadata {
            storage_class: Some(StorageClass::Volatile),
            pointer_hint: Some(PointerHint::PointerLike),
            ..Default::default()
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x200, 8),
            src,
        });
        block.push(R2ILOp::Load {
            dst: reg(0x10, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x200, 8),
        });

        annotate_semantic_metadata_with_hints(
            &mut block,
            "x86-64",
            SemanticMetadataOptions::default(),
            reg_name_resolver(&[(0x10, 8, "rax"), (0x20, 8, "rsp")]),
        );

        let op_meta = block.op_metadata(1).expect("load metadata");
        assert_eq!(op_meta.memory_class, Some(MemoryClass::Mmio));
        assert_eq!(
            op_meta.permissions,
            Some(MemoryPermissions {
                read: true,
                write: false,
                execute: false,
                volatile: true,
                cacheable: false,
            })
        );
    }

    #[test]
    fn semantic_metadata_does_not_downgrade_existing_hints() {
        let mut block = R2ILBlock::new(0x1000, 4);
        let mut addr = reg(0x20, 8);
        addr.meta = Some(r2il::VarnodeMetadata {
            storage_class: Some(StorageClass::Global),
            pointer_hint: Some(PointerHint::CodePointer),
            ..Default::default()
        });
        block.push(R2ILOp::Load {
            dst: reg(0x10, 8),
            space: SpaceId::Ram,
            addr,
        });
        block.set_op_metadata(
            0,
            OpMetadata {
                memory_class: Some(MemoryClass::ThreadLocal),
                permissions: Some(MemoryPermissions {
                    read: true,
                    write: true,
                    execute: false,
                    volatile: true,
                    cacheable: false,
                }),
                ..Default::default()
            },
        );

        annotate_semantic_metadata_with_hints(
            &mut block,
            "x86-64",
            SemanticMetadataOptions::default(),
            reg_name_resolver(&[(0x10, 8, "rax"), (0x20, 8, "rsp")]),
        );

        let R2ILOp::Load { addr, .. } = &block.ops[0] else {
            panic!("expected load");
        };
        let meta = addr.meta.as_ref().expect("address metadata");
        assert_eq!(meta.storage_class, Some(StorageClass::Global));
        assert_eq!(meta.pointer_hint, Some(PointerHint::CodePointer));
        let op_meta = block.op_metadata(0).expect("existing op metadata");
        assert_eq!(op_meta.memory_class, Some(MemoryClass::ThreadLocal));
        assert_eq!(
            op_meta.permissions,
            Some(MemoryPermissions {
                read: true,
                write: true,
                execute: false,
                volatile: true,
                cacheable: false,
            })
        );
    }

    #[test]
    fn semantic_metadata_can_be_disabled() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Load {
            dst: reg(0x10, 8),
            space: SpaceId::Ram,
            addr: reg(0x20, 8),
        });

        annotate_semantic_metadata_with_hints(
            &mut block,
            "x86-64",
            SemanticMetadataOptions {
                enabled: false,
                ..Default::default()
            },
            reg_name_resolver(&[(0x10, 8, "rax"), (0x20, 8, "rsp")]),
        );

        let R2ILOp::Load { addr, .. } = &block.ops[0] else {
            panic!("expected load");
        };
        assert!(addr.meta.is_none(), "metadata should stay disabled");
        assert!(
            block.op_metadata.is_empty(),
            "op metadata should stay disabled"
        );
    }
}
