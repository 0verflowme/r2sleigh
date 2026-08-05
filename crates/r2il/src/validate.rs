//! Structural validation for r2il types.
//!
//! This module provides lightweight structural invariants for architecture
//! specifications and lifted blocks. The checks are intentionally conservative
//! and avoid deep semantic/type reasoning.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::opcode::{R2ILBlock, R2ILOp};
use crate::serialize::ArchSpec;
use crate::{SpaceId, Varnode};

/// A single validation issue.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidationIssue {
    /// Stable machine-readable issue code.
    pub code: &'static str,
    /// Path-like location for the issue.
    pub path: String,
    /// Human-readable description.
    pub message: String,
}

impl ValidationIssue {
    fn new(code: &'static str, path: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            code,
            path: path.into(),
            message: message.into(),
        }
    }
}

/// Aggregated validation error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidationError {
    /// All issues discovered during validation.
    pub issues: Vec<ValidationIssue>,
}

impl ValidationError {
    fn from_issues(issues: Vec<ValidationIssue>) -> Self {
        Self { issues }
    }
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "r2il validation failed with {} issue(s):",
            self.issues.len()
        )?;
        for issue in &self.issues {
            writeln!(f, "  - [{}] {}: {}", issue.code, issue.path, issue.message)?;
        }
        Ok(())
    }
}

impl std::error::Error for ValidationError {}

/// Validate an architecture specification.
pub fn validate_archspec(arch: &ArchSpec) -> Result<(), ValidationError> {
    let mut issues = Vec::new();

    if arch.name.trim().is_empty() {
        issues.push(ValidationIssue::new(
            "arch.name.empty",
            "arch.name",
            "architecture name must not be empty",
        ));
    }
    if arch.addr_size == 0 {
        issues.push(ValidationIssue::new(
            "arch.addr_size.zero",
            "arch.addr_size",
            "address size must be > 0",
        ));
    }
    if arch.alignment == 0 {
        issues.push(ValidationIssue::new(
            "arch.alignment.zero",
            "arch.alignment",
            "alignment must be > 0",
        ));
    }

    let expected_legacy = arch.memory_endianness.to_legacy_big_endian();
    if arch.big_endian != expected_legacy {
        issues.push(ValidationIssue::new(
            "arch.endianness.legacy_mismatch",
            "arch.big_endian",
            format!(
                "legacy big_endian ({}) does not match derived memory endianness ({})",
                arch.big_endian, expected_legacy
            ),
        ));
    }

    if arch.spaces.is_empty() {
        issues.push(ValidationIssue::new(
            "arch.spaces.empty",
            "arch.spaces",
            "at least one address space is required",
        ));
    }

    let default_count = arch.spaces.iter().filter(|s| s.is_default).count();
    if default_count != 1 {
        issues.push(ValidationIssue::new(
            "arch.spaces.default_count",
            "arch.spaces",
            format!(
                "exactly one default address space is required (found {})",
                default_count
            ),
        ));
    }

    let mut seen_space_ids = HashSet::new();
    let mut seen_space_names = HashSet::new();
    for (i, space) in arch.spaces.iter().enumerate() {
        if !seen_space_ids.insert(space.id) {
            issues.push(ValidationIssue::new(
                "arch.spaces.duplicate_id",
                format!("arch.spaces[{i}].id"),
                format!("duplicate space id '{}'", space.id),
            ));
        }
        if !seen_space_names.insert(space.name.clone()) {
            issues.push(ValidationIssue::new(
                "arch.spaces.duplicate_name",
                format!("arch.spaces[{i}].name"),
                format!("duplicate space name '{}'", space.name),
            ));
        }
        if let Some(bank_id) = &space.bank_id
            && bank_id.trim().is_empty()
        {
            issues.push(ValidationIssue::new(
                "arch.space.bank_id.empty",
                format!("arch.spaces[{i}].bank_id"),
                "bank_id must not be empty when present",
            ));
        }
        if let Some(segment_id) = &space.segment_id
            && segment_id.trim().is_empty()
        {
            issues.push(ValidationIssue::new(
                "arch.space.segment_id.empty",
                format!("arch.spaces[{i}].segment_id"),
                "segment_id must not be empty when present",
            ));
        }
        for (range_index, range) in space.valid_ranges.iter().enumerate() {
            if range.start >= range.end {
                issues.push(ValidationIssue::new(
                    "arch.space.range.invalid",
                    format!("arch.spaces[{i}].valid_ranges[{range_index}]"),
                    format!(
                        "invalid half-open range [{:#x}, {:#x}) (start must be < end)",
                        range.start, range.end
                    ),
                ));
            }
        }
    }

    let mut seen_reg_names = HashSet::new();
    let mut reg_by_name = HashMap::new();
    for (i, reg) in arch.registers.iter().enumerate() {
        if reg.size == 0 {
            issues.push(ValidationIssue::new(
                "arch.registers.size.zero",
                format!("arch.registers[{i}].size"),
                "register size must be > 0",
            ));
        }
        if !seen_reg_names.insert(reg.name.clone()) {
            issues.push(ValidationIssue::new(
                "arch.registers.duplicate_name",
                format!("arch.registers[{i}].name"),
                format!("duplicate register name '{}'", reg.name),
            ));
        }
        reg_by_name.insert(reg.name.as_str(), reg.offset);
    }

    for (name, offset) in &arch.register_map {
        match reg_by_name.get(name.as_str()) {
            None => issues.push(ValidationIssue::new(
                "arch.register_map.unknown_register",
                format!("arch.register_map[{name}]"),
                format!("register_map entry references unknown register '{}'", name),
            )),
            Some(reg_offset) if reg_offset != offset => issues.push(ValidationIssue::new(
                "arch.register_map.offset_mismatch",
                format!("arch.register_map[{name}]"),
                format!(
                    "register_map offset {} does not match register offset {}",
                    offset, reg_offset
                ),
            )),
            Some(_) => {}
        }
    }

    for (i, reg) in arch.registers.iter().enumerate() {
        match arch.register_map.get(&reg.name) {
            None => issues.push(ValidationIssue::new(
                "arch.register_map.missing_entry",
                format!("arch.registers[{i}]"),
                format!("missing register_map entry for '{}'", reg.name),
            )),
            Some(offset) if *offset != reg.offset => issues.push(ValidationIssue::new(
                "arch.register_map.offset_mismatch",
                format!("arch.registers[{i}]"),
                format!(
                    "register '{}' offset {} mismatches register_map offset {}",
                    reg.name, reg.offset, offset
                ),
            )),
            Some(_) => {}
        }
    }

    let mut seen_userops = HashSet::new();
    for (i, op) in arch.userops.iter().enumerate() {
        if !seen_userops.insert(op.index) {
            issues.push(ValidationIssue::new(
                "arch.userops.duplicate_index",
                format!("arch.userops[{i}].index"),
                format!("duplicate userop index {}", op.index),
            ));
        }
    }

    if issues.is_empty() {
        Ok(())
    } else {
        Err(ValidationError::from_issues(issues))
    }
}

/// Validate a single operation at a given index.
pub fn validate_op(op: &R2ILOp, op_index: usize) -> Result<(), ValidationError> {
    let mut issues = Vec::new();

    for (input_index, input) in op.inputs().iter().enumerate() {
        validate_varnode(
            &mut issues,
            input,
            format!("block.ops[{op_index}].inputs[{input_index}]"),
            false,
        );
    }

    if let Some(output) = op.output() {
        validate_varnode(
            &mut issues,
            output,
            format!("block.ops[{op_index}].output"),
            true,
        );
    }

    match op {
        R2ILOp::Load { space, .. } if *space == SpaceId::Const => {
            issues.push(ValidationIssue::new(
                "op.load.space_const",
                format!("block.ops[{op_index}].space"),
                "load space must not be const",
            ));
        }
        R2ILOp::LoadLinked { space, .. } if *space == SpaceId::Const => {
            issues.push(ValidationIssue::new(
                "op.load_linked.space_const",
                format!("block.ops[{op_index}].space"),
                "load-linked space must not be const",
            ));
        }
        R2ILOp::Store { space, .. } if *space == SpaceId::Const => {
            issues.push(ValidationIssue::new(
                "op.store.space_const",
                format!("block.ops[{op_index}].space"),
                "store space must not be const",
            ));
        }
        R2ILOp::StoreConditional { space, .. } if *space == SpaceId::Const => {
            issues.push(ValidationIssue::new(
                "op.store_conditional.space_const",
                format!("block.ops[{op_index}].space"),
                "store-conditional space must not be const",
            ));
        }
        R2ILOp::AtomicCAS { space, .. } if *space == SpaceId::Const => {
            issues.push(ValidationIssue::new(
                "op.atomic_cas.space_const",
                format!("block.ops[{op_index}].space"),
                "atomic CAS space must not be const",
            ));
        }
        R2ILOp::LoadGuarded { space, .. } if *space == SpaceId::Const => {
            issues.push(ValidationIssue::new(
                "op.load_guarded.space_const",
                format!("block.ops[{op_index}].space"),
                "guarded load space must not be const",
            ));
        }
        R2ILOp::StoreGuarded { space, .. } if *space == SpaceId::Const => {
            issues.push(ValidationIssue::new(
                "op.store_guarded.space_const",
                format!("block.ops[{op_index}].space"),
                "guarded store space must not be const",
            ));
        }
        R2ILOp::PtrAdd { element_size, .. } if *element_size == 0 => {
            issues.push(ValidationIssue::new(
                "op.ptradd.element_size_zero",
                format!("block.ops[{op_index}].element_size"),
                "PtrAdd element_size must be > 0",
            ));
        }
        R2ILOp::PtrSub { element_size, .. } if *element_size == 0 => {
            issues.push(ValidationIssue::new(
                "op.ptrsub.element_size_zero",
                format!("block.ops[{op_index}].element_size"),
                "PtrSub element_size must be > 0",
            ));
        }
        R2ILOp::Multiequal { inputs, .. } if inputs.is_empty() => {
            issues.push(ValidationIssue::new(
                "op.multiequal.inputs_empty",
                format!("block.ops[{op_index}].inputs"),
                "Multiequal inputs must not be empty",
            ));
        }
        R2ILOp::CallOther {
            output: Some(output),
            ..
        } if output.space == SpaceId::Const => {
            issues.push(ValidationIssue::new(
                "op.callother.output_const",
                format!("block.ops[{op_index}].output"),
                "CallOther output must not be const space",
            ));
        }
        _ => {}
    }

    if issues.is_empty() {
        Ok(())
    } else {
        Err(ValidationError::from_issues(issues))
    }
}

/// Validate a full lifted block.
pub fn validate_block(block: &R2ILBlock) -> Result<(), ValidationError> {
    let mut issues = Vec::new();

    if block.size == 0 {
        issues.push(ValidationIssue::new(
            "block.size.zero",
            "block.size",
            "block size must be > 0",
        ));
    }

    for (i, op) in block.ops.iter().enumerate() {
        if let Err(err) = validate_op(op, i) {
            issues.extend(err.issues);
        }
    }

    for (idx, meta) in &block.op_metadata {
        if *idx >= block.ops.len() {
            issues.push(ValidationIssue::new(
                "block.op_metadata.index_oob",
                format!("block.op_metadata[{idx}]"),
                format!(
                    "op metadata index {} is out of bounds for {} op(s)",
                    idx,
                    block.ops.len()
                ),
            ));
        }
        if let Some(bank_id) = &meta.bank_id
            && bank_id.trim().is_empty()
        {
            issues.push(ValidationIssue::new(
                "block.op_metadata.bank_id.empty",
                format!("block.op_metadata[{idx}].bank_id"),
                "op metadata bank_id must not be empty when present",
            ));
        }
        if let Some(segment_id) = &meta.segment_id
            && segment_id.trim().is_empty()
        {
            issues.push(ValidationIssue::new(
                "block.op_metadata.segment_id.empty",
                format!("block.op_metadata[{idx}].segment_id"),
                "op metadata segment_id must not be empty when present",
            ));
        }
        if let Some(range) = meta.valid_range
            && range.start >= range.end
        {
            issues.push(ValidationIssue::new(
                "block.op_metadata.range.invalid",
                format!("block.op_metadata[{idx}].valid_range"),
                format!(
                    "invalid half-open range [{:#x}, {:#x}) (start must be < end)",
                    range.start, range.end
                ),
            ));
        }
    }

    if let Some(sw) = &block.switch_info {
        if sw.min_val > sw.max_val {
            issues.push(ValidationIssue::new(
                "block.switch.range_invalid",
                "block.switch_info",
                format!(
                    "switch min_val ({}) must be <= max_val ({})",
                    sw.min_val, sw.max_val
                ),
            ));
        }

        let mut seen_case_values = HashSet::new();
        for (i, case) in sw.cases.iter().enumerate() {
            if case.value < sw.min_val || case.value > sw.max_val {
                issues.push(ValidationIssue::new(
                    "block.switch.case_out_of_range",
                    format!("block.switch_info.cases[{i}].value"),
                    format!(
                        "case value {} is outside switch range [{}, {}]",
                        case.value, sw.min_val, sw.max_val
                    ),
                ));
            }
            if !seen_case_values.insert(case.value) {
                issues.push(ValidationIssue::new(
                    "block.switch.duplicate_case_value",
                    format!("block.switch_info.cases[{i}].value"),
                    format!("duplicate switch case value {}", case.value),
                ));
            }
        }
    }

    if issues.is_empty() {
        Ok(())
    } else {
        Err(ValidationError::from_issues(issues))
    }
}

/// Validate a single operation semantic constraints against architecture context.
pub fn validate_op_semantic(
    op: &R2ILOp,
    arch: &ArchSpec,
    op_index: usize,
) -> Result<(), ValidationError> {
    let mut issues = Vec::new();

    match op {
        // Copy / explicit conversion rules
        R2ILOp::Copy { dst, src } => {
            check_size_eq(
                &mut issues,
                "op.copy.width_mismatch",
                op_index,
                "dst.size",
                dst.size,
                "src.size",
                src.size,
            );
        }
        R2ILOp::IntZExt { dst, src } => {
            check_size_gt(
                &mut issues,
                "op.intzext.non_expanding",
                op_index,
                "dst.size",
                dst.size,
                "src.size",
                src.size,
            );
        }
        R2ILOp::IntSExt { dst, src } => {
            check_size_gt(
                &mut issues,
                "op.intsext.non_expanding",
                op_index,
                "dst.size",
                dst.size,
                "src.size",
                src.size,
            );
        }
        R2ILOp::Trunc { dst, src } => {
            check_size_lt(
                &mut issues,
                "op.trunc.non_shrinking",
                op_index,
                "dst.size",
                dst.size,
                "src.size",
                src.size,
            );
        }
        R2ILOp::Select {
            dst,
            cond,
            if_true,
            if_false,
        } => {
            check_size_const(
                &mut issues,
                "op.select.cond_width_mismatch",
                op_index,
                "cond.size",
                cond.size,
                1,
            );
            check_size_eq(
                &mut issues,
                "op.select.width_mismatch",
                op_index,
                "dst.size",
                dst.size,
                "if_true.size",
                if_true.size,
            );
            check_size_eq(
                &mut issues,
                "op.select.width_mismatch",
                op_index,
                "dst.size",
                dst.size,
                "if_false.size",
                if_false.size,
            );
        }

        // Integer arithmetic/bitwise rules
        R2ILOp::IntAdd { dst, a, b }
        | R2ILOp::IntSub { dst, a, b }
        | R2ILOp::IntMult { dst, a, b }
        | R2ILOp::IntDiv { dst, a, b }
        | R2ILOp::IntSDiv { dst, a, b }
        | R2ILOp::IntRem { dst, a, b }
        | R2ILOp::IntSRem { dst, a, b }
        | R2ILOp::IntAnd { dst, a, b }
        | R2ILOp::IntOr { dst, a, b }
        | R2ILOp::IntXor { dst, a, b } => {
            let op_name = semantic_op_name(op);
            check_size_eq(
                &mut issues,
                op_name_width_code(op_name),
                op_index,
                "a.size",
                a.size,
                "b.size",
                b.size,
            );
            check_size_eq(
                &mut issues,
                op_name_width_code(op_name),
                op_index,
                "dst.size",
                dst.size,
                "a.size",
                a.size,
            );
        }
        R2ILOp::IntNegate { dst, src } | R2ILOp::IntNot { dst, src } => {
            let op_name = semantic_op_name(op);
            check_size_eq(
                &mut issues,
                op_name_width_code(op_name),
                op_index,
                "dst.size",
                dst.size,
                "src.size",
                src.size,
            );
        }
        R2ILOp::IntLeft { dst, a, b }
        | R2ILOp::IntRight { dst, a, b }
        | R2ILOp::IntSRight { dst, a, b } => {
            let op_name = semantic_op_name(op);
            check_size_eq(
                &mut issues,
                op_name_width_code(op_name),
                op_index,
                "dst.size",
                dst.size,
                "a.size",
                a.size,
            );
            if b.size == 0 {
                issues.push(ValidationIssue::new(
                    "op.shift.amount_size_zero",
                    format!("block.ops[{op_index}].b.size"),
                    "shift amount size must be > 0",
                ));
            }
        }
        R2ILOp::IntCarry { dst, a, b }
        | R2ILOp::IntSCarry { dst, a, b }
        | R2ILOp::IntSBorrow { dst, a, b } => {
            let op_name = semantic_op_name(op);
            check_size_eq(
                &mut issues,
                op_name_width_code(op_name),
                op_index,
                "a.size",
                a.size,
                "b.size",
                b.size,
            );
            check_size_const(
                &mut issues,
                op_name_width_code(op_name),
                op_index,
                "dst.size",
                dst.size,
                1,
            );
        }

        // Compare/boolean rules
        R2ILOp::IntEqual { dst, a, b }
        | R2ILOp::IntNotEqual { dst, a, b }
        | R2ILOp::IntLess { dst, a, b }
        | R2ILOp::IntSLess { dst, a, b }
        | R2ILOp::IntLessEqual { dst, a, b }
        | R2ILOp::IntSLessEqual { dst, a, b } => {
            let op_name = semantic_op_name(op);
            check_size_eq(
                &mut issues,
                op_name_width_code(op_name),
                op_index,
                "a.size",
                a.size,
                "b.size",
                b.size,
            );
            check_size_const(
                &mut issues,
                op_name_width_code(op_name),
                op_index,
                "dst.size",
                dst.size,
                1,
            );
        }
        R2ILOp::BoolNot { dst, src } => {
            check_size_const(
                &mut issues,
                "op.boolnot.width_mismatch",
                op_index,
                "src.size",
                src.size,
                1,
            );
            check_size_const(
                &mut issues,
                "op.boolnot.width_mismatch",
                op_index,
                "dst.size",
                dst.size,
                1,
            );
        }
        R2ILOp::BoolAnd { dst, a, b }
        | R2ILOp::BoolOr { dst, a, b }
        | R2ILOp::BoolXor { dst, a, b } => {
            let op_name = semantic_op_name(op);
            check_size_const(
                &mut issues,
                op_name_width_code(op_name),
                op_index,
                "a.size",
                a.size,
                1,
            );
            check_size_const(
                &mut issues,
                op_name_width_code(op_name),
                op_index,
                "b.size",
                b.size,
                1,
            );
            check_size_const(
                &mut issues,
                op_name_width_code(op_name),
                op_index,
                "dst.size",
                dst.size,
                1,
            );
        }

        // Memory rules
        R2ILOp::Load { dst, space, addr } => {
            let arch_expected = effective_arch_addr_size(arch);
            let expected = addr_space_size(*space, arch);
            check_size_addr_width(
                &mut issues,
                "op.load.addr_width_mismatch",
                op_index,
                "addr.size",
                addr.size,
                expected,
                arch_expected,
            );
            check_const_memory_access(
                &mut issues,
                arch,
                op_index,
                *space,
                addr,
                dst.size,
                true,
                false,
                "op.load.range",
                "op.load.permission",
            );
        }
        R2ILOp::LoadLinked {
            dst, space, addr, ..
        } => {
            let arch_expected = effective_arch_addr_size(arch);
            let expected = addr_space_size(*space, arch);
            check_size_addr_width(
                &mut issues,
                "op.load_linked.addr_width_mismatch",
                op_index,
                "addr.size",
                addr.size,
                expected,
                arch_expected,
            );
            check_const_memory_access(
                &mut issues,
                arch,
                op_index,
                *space,
                addr,
                dst.size,
                true,
                false,
                "op.load_linked.range",
                "op.load_linked.permission",
            );
        }
        R2ILOp::Store {
            space, addr, val, ..
        } => {
            let arch_expected = effective_arch_addr_size(arch);
            let expected = addr_space_size(*space, arch);
            check_size_addr_width(
                &mut issues,
                "op.store.addr_width_mismatch",
                op_index,
                "addr.size",
                addr.size,
                expected,
                arch_expected,
            );
            check_const_memory_access(
                &mut issues,
                arch,
                op_index,
                *space,
                addr,
                val.size,
                false,
                true,
                "op.store.range",
                "op.store.permission",
            );
        }
        R2ILOp::StoreConditional {
            result,
            space,
            addr,
            val,
            ..
        } => {
            let arch_expected = effective_arch_addr_size(arch);
            let expected = addr_space_size(*space, arch);
            check_size_addr_width(
                &mut issues,
                "op.store_conditional.addr_width_mismatch",
                op_index,
                "addr.size",
                addr.size,
                expected,
                arch_expected,
            );
            if let Some(result) = result
                && result.size == 0
            {
                issues.push(ValidationIssue::new(
                    "op.store_conditional.result_size_zero",
                    format!("block.ops[{op_index}].result.size"),
                    "store-conditional result size must be > 0 when present",
                ));
            }
            check_const_memory_access(
                &mut issues,
                arch,
                op_index,
                *space,
                addr,
                val.size,
                false,
                true,
                "op.store_conditional.range",
                "op.store_conditional.permission",
            );
        }
        R2ILOp::AtomicCAS {
            dst,
            space,
            addr,
            expected,
            replacement,
            ..
        } => {
            check_size_eq(
                &mut issues,
                "op.atomic_cas.width",
                op_index,
                "dst.size",
                dst.size,
                "expected.size",
                expected.size,
            );
            check_size_eq(
                &mut issues,
                "op.atomic_cas.width",
                op_index,
                "dst.size",
                dst.size,
                "replacement.size",
                replacement.size,
            );
            let arch_expected = effective_arch_addr_size(arch);
            let expected_addr = addr_space_size(*space, arch);
            check_size_addr_width(
                &mut issues,
                "op.atomic_cas.addr_width_mismatch",
                op_index,
                "addr.size",
                addr.size,
                expected_addr,
                arch_expected,
            );
            check_const_memory_access(
                &mut issues,
                arch,
                op_index,
                *space,
                addr,
                dst.size,
                true,
                true,
                "op.atomic_cas.range",
                "op.atomic_cas.permission",
            );
        }
        R2ILOp::LoadGuarded {
            dst,
            space,
            addr,
            guard,
            ..
        } => {
            check_size_const(
                &mut issues,
                "op.load_guarded.guard_size",
                op_index,
                "guard.size",
                guard.size,
                1,
            );
            let arch_expected = effective_arch_addr_size(arch);
            let expected = addr_space_size(*space, arch);
            check_size_addr_width(
                &mut issues,
                "op.load_guarded.addr_width_mismatch",
                op_index,
                "addr.size",
                addr.size,
                expected,
                arch_expected,
            );
            check_const_memory_access(
                &mut issues,
                arch,
                op_index,
                *space,
                addr,
                dst.size,
                true,
                false,
                "op.load_guarded.range",
                "op.load_guarded.permission",
            );
        }
        R2ILOp::StoreGuarded {
            space,
            addr,
            val,
            guard,
            ..
        } => {
            check_size_const(
                &mut issues,
                "op.store_guarded.guard_size",
                op_index,
                "guard.size",
                guard.size,
                1,
            );
            let arch_expected = effective_arch_addr_size(arch);
            let expected = addr_space_size(*space, arch);
            check_size_addr_width(
                &mut issues,
                "op.store_guarded.addr_width_mismatch",
                op_index,
                "addr.size",
                addr.size,
                expected,
                arch_expected,
            );
            check_const_memory_access(
                &mut issues,
                arch,
                op_index,
                *space,
                addr,
                val.size,
                false,
                true,
                "op.store_guarded.range",
                "op.store_guarded.permission",
            );
        }

        // Piece/Subpiece rules
        R2ILOp::Piece { dst, hi, lo } => {
            let expected = hi.size.saturating_add(lo.size);
            check_size_const(
                &mut issues,
                "op.piece.width_mismatch",
                op_index,
                "dst.size",
                dst.size,
                expected,
            );
        }
        R2ILOp::Subpiece { dst, src, offset } => {
            let src_size = src.size;
            if *offset >= src_size {
                issues.push(ValidationIssue::new(
                    "op.subpiece.offset_oob",
                    format!("block.ops[{op_index}].offset"),
                    format!(
                        "subpiece offset {} is out of bounds for src size {}",
                        offset, src_size
                    ),
                ));
            } else if offset.saturating_add(dst.size) > src_size {
                issues.push(ValidationIssue::new(
                    "op.subpiece.width_oob",
                    format!("block.ops[{op_index}].dst.size"),
                    format!(
                        "subpiece range offset {} + dst.size {} exceeds src size {}",
                        offset, dst.size, src_size
                    ),
                ));
            }
        }

        // Control-flow target rules
        R2ILOp::Branch { target }
        | R2ILOp::BranchInd { target }
        | R2ILOp::Call { target }
        | R2ILOp::CallInd { target }
        | R2ILOp::Return { target } => {
            if target.space != SpaceId::Const {
                let arch_expected = effective_arch_addr_size(arch);
                check_size_const(
                    &mut issues,
                    "op.controlflow.target_width_mismatch",
                    op_index,
                    "target.size",
                    target.size,
                    arch_expected,
                );
            }
        }
        R2ILOp::CBranch { target, cond } => {
            if target.space != SpaceId::Const {
                let arch_expected = effective_arch_addr_size(arch);
                check_size_const(
                    &mut issues,
                    "op.cbranch.target_width_mismatch",
                    op_index,
                    "target.size",
                    target.size,
                    arch_expected,
                );
            }
            check_size_const(
                &mut issues,
                "op.cbranch.cond_width_mismatch",
                op_index,
                "cond.size",
                cond.size,
                1,
            );
        }
        _ => {}
    }

    if issues.is_empty() {
        Ok(())
    } else {
        Err(ValidationError::from_issues(issues))
    }
}

/// Validate semantic constraints for a full lifted block.
pub fn validate_block_semantic(block: &R2ILBlock, arch: &ArchSpec) -> Result<(), ValidationError> {
    let mut issues = Vec::new();

    for (i, op) in block.ops.iter().enumerate() {
        if let Err(err) = validate_op_semantic(op, arch, i) {
            issues.extend(err.issues);
        }
    }

    if issues.is_empty() {
        Ok(())
    } else {
        Err(ValidationError::from_issues(issues))
    }
}

/// Validate both structural and semantic constraints for a lifted block.
pub fn validate_block_full(block: &R2ILBlock, arch: &ArchSpec) -> Result<(), ValidationError> {
    let mut issues = Vec::new();

    if let Err(err) = validate_block(block) {
        issues.extend(err.issues);
    }
    if let Err(err) = validate_block_semantic(block, arch) {
        issues.extend(err.issues);
    }

    if issues.is_empty() {
        Ok(())
    } else {
        Err(ValidationError::from_issues(issues))
    }
}

fn validate_varnode(
    issues: &mut Vec<ValidationIssue>,
    vn: &Varnode,
    path: String,
    is_output: bool,
) {
    if vn.size == 0 {
        issues.push(ValidationIssue::new(
            "varnode.size.zero",
            format!("{path}.size"),
            "varnode size must be > 0",
        ));
    }
    if is_output && vn.space == SpaceId::Const {
        issues.push(ValidationIssue::new(
            "varnode.output_const_space",
            format!("{path}.space"),
            "output/destination varnode must not be const space",
        ));
    }

    if let Some(meta) = &vn.meta {
        if let Some(bank_id) = &meta.bank_id
            && bank_id.trim().is_empty()
        {
            issues.push(ValidationIssue::new(
                "varnode.meta.bank_id.empty",
                format!("{path}.meta.bank_id"),
                "metadata bank_id must not be empty when present",
            ));
        }
        if let Some(segment_id) = &meta.segment_id
            && segment_id.trim().is_empty()
        {
            issues.push(ValidationIssue::new(
                "varnode.meta.segment_id.empty",
                format!("{path}.meta.segment_id"),
                "metadata segment_id must not be empty when present",
            ));
        }
        if let Some(range) = meta.valid_range
            && range.start >= range.end
        {
            issues.push(ValidationIssue::new(
                "varnode.meta.range.invalid",
                format!("{path}.meta.valid_range"),
                format!(
                    "invalid half-open range [{:#x}, {:#x}) (start must be < end)",
                    range.start, range.end
                ),
            ));
        }
    }
}

fn addr_space_size(space: SpaceId, arch: &ArchSpec) -> u32 {
    let arch_size = effective_arch_addr_size(arch);
    let space_size = arch
        .spaces
        .iter()
        .find(|s| s.id == space)
        .map(|s| s.addr_size)
        .unwrap_or(arch_size);

    if space_size <= 1 {
        arch_size
    } else {
        space_size
    }
}

fn effective_arch_addr_size(arch: &ArchSpec) -> u32 {
    if arch.addr_size > 1 {
        return arch.addr_size;
    }

    if let Some(pc_size) = arch
        .registers
        .iter()
        .find(|r| {
            matches!(
                r.name.to_ascii_lowercase().as_str(),
                "pc" | "ip" | "eip" | "rip"
            )
        })
        .map(|r| r.size)
        .filter(|size| *size > 1)
    {
        return pc_size;
    }

    if let Some(default_size) = arch
        .spaces
        .iter()
        .find(|s| s.is_default && s.addr_size > 1)
        .map(|s| s.addr_size)
    {
        return default_size;
    }

    arch.spaces
        .iter()
        .map(|s| s.addr_size)
        .max()
        .filter(|size| *size > 1)
        .unwrap_or(arch.addr_size.max(1))
}

fn semantic_op_name(op: &R2ILOp) -> &'static str {
    match op {
        R2ILOp::IntAdd { .. } => "intadd",
        R2ILOp::IntSub { .. } => "intsub",
        R2ILOp::IntMult { .. } => "intmult",
        R2ILOp::IntDiv { .. } => "intdiv",
        R2ILOp::IntSDiv { .. } => "intsdiv",
        R2ILOp::IntRem { .. } => "intrem",
        R2ILOp::IntSRem { .. } => "intsrem",
        R2ILOp::IntAnd { .. } => "intand",
        R2ILOp::IntOr { .. } => "intor",
        R2ILOp::IntXor { .. } => "intxor",
        R2ILOp::IntNegate { .. } => "intnegate",
        R2ILOp::IntNot { .. } => "intnot",
        R2ILOp::IntLeft { .. } => "intleft",
        R2ILOp::IntRight { .. } => "intright",
        R2ILOp::IntSRight { .. } => "intsright",
        R2ILOp::IntCarry { .. } => "intcarry",
        R2ILOp::IntSCarry { .. } => "intscarry",
        R2ILOp::IntSBorrow { .. } => "intsborrow",
        R2ILOp::IntEqual { .. } => "intequal",
        R2ILOp::IntNotEqual { .. } => "intnotequal",
        R2ILOp::IntLess { .. } => "intless",
        R2ILOp::IntSLess { .. } => "intsless",
        R2ILOp::IntLessEqual { .. } => "intlessequal",
        R2ILOp::IntSLessEqual { .. } => "intslessequal",
        R2ILOp::BoolAnd { .. } => "booland",
        R2ILOp::BoolOr { .. } => "boolor",
        R2ILOp::BoolXor { .. } => "boolxor",
        _ => "op",
    }
}

#[allow(clippy::too_many_arguments)]
fn check_const_memory_access(
    issues: &mut Vec<ValidationIssue>,
    arch: &ArchSpec,
    op_index: usize,
    space_id: SpaceId,
    addr: &Varnode,
    access_size: u32,
    needs_read: bool,
    needs_write: bool,
    range_code: &'static str,
    permission_code: &'static str,
) {
    if addr.space != SpaceId::Const {
        return;
    }

    let Some(space) = arch.spaces.iter().find(|s| s.id == space_id) else {
        return;
    };

    if !space.valid_ranges.is_empty()
        && !space
            .valid_ranges
            .iter()
            .any(|range| range.contains_interval(addr.offset, access_size))
    {
        issues.push(ValidationIssue::new(
            range_code,
            format!("block.ops[{op_index}].addr"),
            format!(
                "const address {:#x} size {} is outside configured ranges for space '{}'",
                addr.offset, access_size, space.name
            ),
        ));
    }

    if let Some(perms) = space.permissions {
        if needs_read && !perms.read {
            issues.push(ValidationIssue::new(
                permission_code,
                format!("block.ops[{op_index}].space"),
                format!(
                    "space '{}' denies read access for const-address memory operation",
                    space.name
                ),
            ));
        }
        if needs_write && !perms.write {
            issues.push(ValidationIssue::new(
                permission_code,
                format!("block.ops[{op_index}].space"),
                format!(
                    "space '{}' denies write access for const-address memory operation",
                    space.name
                ),
            ));
        }
    }
}

fn op_name_width_code(op_name: &str) -> &'static str {
    match op_name {
        "intadd" => "op.intadd.width_mismatch",
        "intsub" => "op.intsub.width_mismatch",
        "intmult" => "op.intmult.width_mismatch",
        "intdiv" => "op.intdiv.width_mismatch",
        "intsdiv" => "op.intsdiv.width_mismatch",
        "intrem" => "op.intrem.width_mismatch",
        "intsrem" => "op.intsrem.width_mismatch",
        "intand" => "op.intand.width_mismatch",
        "intor" => "op.intor.width_mismatch",
        "intxor" => "op.intxor.width_mismatch",
        "intnegate" => "op.intnegate.width_mismatch",
        "intnot" => "op.intnot.width_mismatch",
        "intleft" => "op.intleft.width_mismatch",
        "intright" => "op.intright.width_mismatch",
        "intsright" => "op.intsright.width_mismatch",
        "intcarry" => "op.intcarry.width_mismatch",
        "intscarry" => "op.intscarry.width_mismatch",
        "intsborrow" => "op.intsborrow.width_mismatch",
        "intequal" => "op.intequal.width_mismatch",
        "intnotequal" => "op.intnotequal.width_mismatch",
        "intless" => "op.intless.width_mismatch",
        "intsless" => "op.intsless.width_mismatch",
        "intlessequal" => "op.intlessequal.width_mismatch",
        "intslessequal" => "op.intslessequal.width_mismatch",
        "booland" => "op.booland.width_mismatch",
        "boolor" => "op.boolor.width_mismatch",
        "boolxor" => "op.boolxor.width_mismatch",
        _ => "op.width_mismatch",
    }
}

fn check_size_eq(
    issues: &mut Vec<ValidationIssue>,
    code: &'static str,
    op_index: usize,
    left_name: &str,
    left: u32,
    right_name: &str,
    right: u32,
) {
    if left != right {
        issues.push(ValidationIssue::new(
            code,
            format!("block.ops[{op_index}]"),
            format!(
                "{} ({}) must equal {} ({})",
                left_name, left, right_name, right
            ),
        ));
    }
}

fn check_size_gt(
    issues: &mut Vec<ValidationIssue>,
    code: &'static str,
    op_index: usize,
    left_name: &str,
    left: u32,
    right_name: &str,
    right: u32,
) {
    if left <= right {
        issues.push(ValidationIssue::new(
            code,
            format!("block.ops[{op_index}]"),
            format!(
                "{} ({}) must be greater than {} ({})",
                left_name, left, right_name, right
            ),
        ));
    }
}

fn check_size_lt(
    issues: &mut Vec<ValidationIssue>,
    code: &'static str,
    op_index: usize,
    left_name: &str,
    left: u32,
    right_name: &str,
    right: u32,
) {
    if left >= right {
        issues.push(ValidationIssue::new(
            code,
            format!("block.ops[{op_index}]"),
            format!(
                "{} ({}) must be less than {} ({})",
                left_name, left, right_name, right
            ),
        ));
    }
}

fn check_size_const(
    issues: &mut Vec<ValidationIssue>,
    code: &'static str,
    op_index: usize,
    field_name: &str,
    actual: u32,
    expected: u32,
) {
    if actual != expected {
        issues.push(ValidationIssue::new(
            code,
            format!("block.ops[{op_index}].{field_name}"),
            format!("expected size {}, got {}", expected, actual),
        ));
    }
}

fn check_size_addr_width(
    issues: &mut Vec<ValidationIssue>,
    code: &'static str,
    op_index: usize,
    field_name: &str,
    actual: u32,
    space_expected: u32,
    arch_expected: u32,
) {
    if actual == space_expected || actual == arch_expected {
        return;
    }

    let message = if space_expected == arch_expected {
        format!("expected size {}, got {}", space_expected, actual)
    } else {
        format!(
            "expected size {} (space) or {} (arch), got {}",
            space_expected, arch_expected, actual
        )
    };

    issues.push(ValidationIssue::new(
        code,
        format!("block.ops[{op_index}].{field_name}"),
        message,
    ));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::opcode::{SwitchCase, SwitchInfo};
    use crate::serialize::{RegisterDef, UserOpDef};
    use crate::{AddressSpace, Endianness, R2ILOp};

    fn valid_archspec() -> ArchSpec {
        let mut arch = ArchSpec::new("test-arch");
        arch.addr_size = 8;
        arch.alignment = 1;
        arch.add_space(AddressSpace::ram(8));
        arch.add_space(AddressSpace::register());
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.userops.push(UserOpDef {
            index: 0,
            name: "u0".to_string(),
        });
        arch
    }

    fn valid_block() -> R2ILBlock {
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(1, 8),
        });
        block
    }

    #[test]
    fn valid_minimal_block_passes() {
        let block = valid_block();
        assert!(validate_block(&block).is_ok());
    }

    #[test]
    fn valid_semantic_block_passes() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(8, 8),
            b: Varnode::constant(1, 8),
        });
        assert!(validate_block_semantic(&block, &arch).is_ok());
        assert!(validate_block_full(&block, &arch).is_ok());
    }

    #[test]
    fn zero_size_varnode_fails() {
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::new(SpaceId::Const, 1, 0),
        });
        let err = validate_block(&block).expect_err("block should fail");
        assert!(err.issues.iter().any(|i| i.code == "varnode.size.zero"));
    }

    #[test]
    fn const_space_destination_fails() {
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Copy {
            dst: Varnode::new(SpaceId::Const, 0, 8),
            src: Varnode::register(0, 8),
        });
        let err = validate_block(&block).expect_err("block should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "varnode.output_const_space")
        );
    }

    #[test]
    fn invalid_load_store_space_fails() {
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0, 8),
            space: SpaceId::Const,
            addr: Varnode::ram(0x2000, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Const,
            addr: Varnode::ram(0x2000, 8),
            val: Varnode::register(0, 8),
        });
        let err = validate_block(&block).expect_err("block should fail");
        assert!(err.issues.iter().any(|i| i.code == "op.load.space_const"));
        assert!(err.issues.iter().any(|i| i.code == "op.store.space_const"));
    }

    #[test]
    fn zero_element_size_in_ptr_ops_fails() {
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::PtrAdd {
            dst: Varnode::register(0, 8),
            base: Varnode::register(8, 8),
            index: Varnode::register(16, 8),
            element_size: 0,
        });
        block.push(R2ILOp::PtrSub {
            dst: Varnode::register(0, 8),
            base: Varnode::register(8, 8),
            index: Varnode::register(16, 8),
            element_size: 0,
        });
        let err = validate_block(&block).expect_err("block should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.ptradd.element_size_zero")
        );
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.ptrsub.element_size_zero")
        );
    }

    #[test]
    fn multiequal_inputs_empty_fails() {
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Multiequal {
            dst: Varnode::register(0, 8),
            inputs: Vec::new(),
        });
        let err = validate_block(&block).expect_err("block should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.multiequal.inputs_empty")
        );
    }

    #[test]
    fn callother_output_const_fails() {
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::CallOther {
            output: Some(Varnode::new(SpaceId::Const, 0, 8)),
            userop: 1,
            inputs: vec![Varnode::register(0, 8)],
        });
        let err = validate_block(&block).expect_err("block should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.callother.output_const")
        );
    }

    #[test]
    fn invalid_switch_metadata_fails() {
        let mut block = valid_block();
        block.switch_info = Some(SwitchInfo {
            switch_addr: 0x1000,
            min_val: 10,
            max_val: 5,
            default_target: Some(0x1200),
            cases: vec![
                SwitchCase {
                    value: 11,
                    target: 0x1300,
                },
                SwitchCase {
                    value: 11,
                    target: 0x1400,
                },
            ],
        });

        let err = validate_block(&block).expect_err("block should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "block.switch.range_invalid")
        );
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "block.switch.case_out_of_range")
        );
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "block.switch.duplicate_case_value")
        );
    }

    #[test]
    fn invalid_archspec_duplicate_default_and_register_map_mismatch_fails() {
        let mut arch = valid_archspec();

        arch.spaces.push(AddressSpace::new(SpaceId::Ram, "ram2", 8));
        if let Some(space) = arch.spaces.last_mut() {
            space.is_default = true;
        }

        arch.registers.push(RegisterDef::new("RAX", 8, 8));
        arch.register_map.insert("RAX".to_string(), 0xdeadbeef);
        arch.register_map.insert("MISSING".to_string(), 0x10);
        arch.userops.push(UserOpDef {
            index: 0,
            name: "u0_duplicate".to_string(),
        });

        let err = validate_archspec(&arch).expect_err("arch should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "arch.spaces.default_count")
        );
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "arch.registers.duplicate_name")
        );
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "arch.register_map.offset_mismatch")
        );
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "arch.register_map.unknown_register")
        );
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "arch.userops.duplicate_index")
        );
    }

    #[test]
    fn validator_flags_legacy_mismatch_when_inconsistent() {
        let mut arch = valid_archspec();
        arch.memory_endianness = Endianness::Big;
        arch.big_endian = false;
        let err = validate_archspec(&arch).expect_err("arch should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "arch.endianness.legacy_mismatch")
        );
    }

    #[test]
    fn copy_width_mismatch_fails() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::register(8, 4),
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.copy.width_mismatch")
        );
    }

    #[test]
    fn intadd_width_mismatch_fails() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(8, 4),
            b: Varnode::register(16, 4),
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.intadd.width_mismatch")
        );
    }

    #[test]
    fn select_width_mismatch_fails() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Select {
            dst: Varnode::register(0, 8),
            cond: Varnode::register(8, 4),
            if_true: Varnode::register(16, 8),
            if_false: Varnode::register(24, 4),
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(
            err.issues
                .iter()
                .any(|issue| issue.code == "op.select.cond_width_mismatch")
        );
        assert!(
            err.issues
                .iter()
                .any(|issue| issue.code == "op.select.width_mismatch")
        );
    }

    #[test]
    fn intcarry_dst_not_one_byte_fails() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::IntCarry {
            dst: Varnode::register(0, 8),
            a: Varnode::register(8, 8),
            b: Varnode::register(16, 8),
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.intcarry.width_mismatch")
        );
    }

    #[test]
    fn compare_dst_not_one_byte_fails() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::IntEqual {
            dst: Varnode::register(0, 8),
            a: Varnode::register(8, 8),
            b: Varnode::register(16, 8),
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.intequal.width_mismatch")
        );
    }

    #[test]
    fn zext_and_sext_non_expanding_fail() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::IntZExt {
            dst: Varnode::register(0, 4),
            src: Varnode::register(8, 4),
        });
        block.push(R2ILOp::IntSExt {
            dst: Varnode::register(0, 4),
            src: Varnode::register(8, 4),
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.intzext.non_expanding")
        );
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.intsext.non_expanding")
        );
    }

    #[test]
    fn trunc_non_shrinking_fails() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Trunc {
            dst: Varnode::register(0, 8),
            src: Varnode::register(8, 8),
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.trunc.non_shrinking")
        );
    }

    #[test]
    fn load_store_addr_width_mismatch_fails() {
        let mut arch = valid_archspec();
        arch.addr_size = 8;
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(8, 4),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(8, 4),
            val: Varnode::register(16, 8),
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.load.addr_width_mismatch")
        );
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.store.addr_width_mismatch")
        );
    }

    #[test]
    fn piece_and_subpiece_bounds_fail() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Piece {
            dst: Varnode::register(0, 4),
            hi: Varnode::register(8, 4),
            lo: Varnode::register(16, 4),
        });
        block.push(R2ILOp::Subpiece {
            dst: Varnode::register(0, 4),
            src: Varnode::register(8, 4),
            offset: 4,
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.piece.width_mismatch")
        );
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.subpiece.offset_oob")
        );
    }

    #[test]
    fn non_const_branch_target_width_mismatch_fails() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Branch {
            target: Varnode::ram(0x2000, 4),
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.controlflow.target_width_mismatch")
        );
    }

    #[test]
    fn const_space_branch_target_allowed() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Branch {
            target: Varnode::constant(0x2000, 4),
        });
        assert!(validate_block_semantic(&block, &arch).is_ok());
    }

    #[test]
    fn cbranch_cond_width_mismatch_fails() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::CBranch {
            target: Varnode::ram(0x2000, 8),
            cond: Varnode::register(0, 8),
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.cbranch.cond_width_mismatch")
        );
    }

    #[test]
    fn semantic_multi_issue_aggregation() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::register(8, 4),
        });
        block.push(R2ILOp::IntCarry {
            dst: Varnode::register(0, 2),
            a: Varnode::register(8, 8),
            b: Varnode::register(16, 4),
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(err.issues.len() >= 3);
    }

    #[test]
    fn arch_space_invalid_range_fails() {
        let mut arch = valid_archspec();
        arch.spaces[0].valid_ranges.push(crate::MemoryRange {
            start: 0x2000,
            end: 0x2000,
        });
        let err = validate_archspec(&arch).expect_err("arch should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "arch.space.range.invalid")
        );
    }

    #[test]
    fn memory_semantic_guard_and_width_checks_fail() {
        let arch = valid_archspec();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::AtomicCAS {
            dst: Varnode::register(0, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(8, 4),
            expected: Varnode::register(16, 4),
            replacement: Varnode::register(24, 8),
            ordering: crate::MemoryOrdering::Relaxed,
        });
        block.push(R2ILOp::LoadGuarded {
            dst: Varnode::register(0, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(8, 8),
            guard: Varnode::register(16, 8),
            ordering: crate::MemoryOrdering::Relaxed,
        });
        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(err.issues.iter().any(|i| i.code == "op.atomic_cas.width"));
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.atomic_cas.addr_width_mismatch")
        );
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "op.load_guarded.guard_size")
        );
    }

    #[test]
    fn const_address_range_and_permission_checks() {
        let mut arch = valid_archspec();
        arch.spaces[0].valid_ranges.push(crate::MemoryRange {
            start: 0x1000,
            end: 0x1008,
        });
        arch.spaces[0].permissions = Some(crate::MemoryPermissions {
            read: true,
            write: false,
            execute: false,
            volatile: false,
            cacheable: true,
        });

        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x1004, 8),
            val: Varnode::register(0, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(8, 8),
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2000, 8),
        });

        let err = validate_block_semantic(&block, &arch).expect_err("semantic should fail");
        assert!(err.issues.iter().any(|i| i.code == "op.store.permission"));
        assert!(err.issues.iter().any(|i| i.code == "op.load.range"));
    }

    #[test]
    fn symbolic_memory_address_skips_range_permission_enforcement() {
        let mut arch = valid_archspec();
        arch.spaces[0].valid_ranges.push(crate::MemoryRange {
            start: 0x1000,
            end: 0x1010,
        });
        arch.spaces[0].permissions = Some(crate::MemoryPermissions {
            read: false,
            write: false,
            execute: false,
            volatile: false,
            cacheable: true,
        });
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(8, 8),
        });
        assert!(validate_block_semantic(&block, &arch).is_ok());
    }

    #[test]
    fn const_load_range_checks_use_full_load_width() {
        let mut arch = valid_archspec();
        arch.spaces[0].valid_ranges.push(crate::MemoryRange {
            start: 0x1000,
            end: 0x1008,
        });

        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0, 8),
            space: SpaceId::Ram,
            // Address is inside range for 1-byte access but out-of-range for 8-byte access.
            addr: Varnode::constant(0x1007, 8),
        });

        let err = validate_block_semantic(&block, &arch).expect_err("load should fail range check");
        assert!(err.issues.iter().any(|i| i.code == "op.load.range"));
    }

    #[test]
    fn block_op_metadata_valid_index_passes() {
        let mut block = valid_block();
        block.set_op_metadata(0, crate::OpMetadata::default());
        assert!(validate_block(&block).is_ok());
    }

    #[test]
    fn block_op_metadata_oob_fails() {
        let mut block = valid_block();
        block.set_op_metadata(2, crate::OpMetadata::default());
        let err = validate_block(&block).expect_err("block should fail");
        assert!(
            err.issues
                .iter()
                .any(|i| i.code == "block.op_metadata.index_oob")
        );
    }

    #[test]
    fn block_op_metadata_json_omits_when_empty() {
        let block = valid_block();
        let json = serde_json::to_string(&block).expect("serialize");
        assert!(
            !json.contains("op_metadata"),
            "op_metadata should be omitted when empty"
        );
    }

    #[test]
    fn block_op_metadata_json_present_when_set() {
        let mut block = valid_block();
        block.set_op_metadata(0, crate::OpMetadata::default());
        let json = serde_json::to_string(&block).expect("serialize");
        assert!(
            json.contains("op_metadata"),
            "op_metadata should be serialized"
        );
    }
}
