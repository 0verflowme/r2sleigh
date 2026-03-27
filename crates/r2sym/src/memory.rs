//! Symbolic memory model for symbolic execution.
//!
//! The memory core is region-based: concrete and symbolic bytes live under
//! explicit stack/global/input/heap/replay/unknown regions. The public API
//! remains address-shaped for compatibility with the executor and summaries.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use z3::ast::{Ast, BV, Bool};
use z3::{Context, SatResult, Solver};

use crate::value::SymValue;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct MemoryRegionId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum MemoryRegionKind {
    Stack,
    Global,
    Input,
    Heap,
    Replay,
    EscapedUnknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RegionPointer {
    pub region_id: MemoryRegionId,
    pub offset: u64,
    pub ptr_bits: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicMemoryRegionDef {
    pub id: MemoryRegionId,
    pub kind: MemoryRegionKind,
    pub name: String,
    pub base_addr: Option<u64>,
    pub extent: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedPointerSet {
    pub pointers: Vec<RegionPointer>,
    pub truncated: bool,
}

#[derive(Clone)]
enum RegionWriteTarget<'ctx> {
    Offset(u64),
    Address(SymValue<'ctx>),
}

#[derive(Clone)]
struct RegionWrite<'ctx> {
    target: RegionWriteTarget<'ctx>,
    value: SymValue<'ctx>,
    size: u32,
}

#[derive(Clone)]
struct MemoryRegion<'ctx> {
    def: SymbolicMemoryRegionDef,
    concrete: BTreeMap<u64, u8>,
    symbolic_writes: Vec<RegionWrite<'ctx>>,
}

impl<'ctx> MemoryRegion<'ctx> {
    fn new(
        id: MemoryRegionId,
        kind: MemoryRegionKind,
        name: impl Into<String>,
        base_addr: Option<u64>,
        extent: Option<u64>,
    ) -> Self {
        Self {
            def: SymbolicMemoryRegionDef {
                id,
                kind,
                name: name.into(),
                base_addr,
                extent,
            },
            concrete: BTreeMap::new(),
            symbolic_writes: Vec::new(),
        }
    }

    fn contains_absolute_range(&self, addr: u64, size: u32) -> bool {
        let Some(base_addr) = self.def.base_addr else {
            return false;
        };
        let Some(offset) = addr.checked_sub(base_addr) else {
            return false;
        };
        self.contains_offset_range(offset, size)
    }

    fn absolute_to_offset(&self, addr: u64) -> Option<u64> {
        let base = self.def.base_addr?;
        addr.checked_sub(base)
    }

    fn contains_offset_range(&self, offset: u64, size: u32) -> bool {
        match self.def.extent {
            Some(extent) => offset
                .checked_add(size as u64)
                .is_some_and(|end| end <= extent),
            None => true,
        }
    }

    fn ensure_extent_covers(&mut self, offset: u64, size: u32) {
        let needed = offset.saturating_add(size as u64);
        match self.def.extent {
            Some(extent) if extent >= needed => {}
            _ => self.def.extent = Some(needed),
        }
    }

    fn merge_offsets(&self) -> BTreeSet<u64> {
        let mut offsets = BTreeSet::new();
        offsets.extend(self.concrete.keys().copied());
        for write in &self.symbolic_writes {
            if let RegionWriteTarget::Offset(base) = write.target {
                for index in 0..write.size {
                    offsets.insert(base.wrapping_add(index as u64));
                }
            }
        }
        offsets
    }

    fn unresolved_symbolic_writes(&self) -> impl Iterator<Item = &RegionWrite<'ctx>> {
        self.symbolic_writes
            .iter()
            .filter(|write| matches!(write.target, RegionWriteTarget::Address(_)))
    }

    fn read_offset(
        &self,
        ctx: &'ctx Context,
        offset: u64,
        size: u32,
        default_symbolic: bool,
        default_name: &str,
    ) -> SymValue<'ctx> {
        for write in self.symbolic_writes.iter().rev() {
            let RegionWriteTarget::Offset(base) = write.target else {
                continue;
            };
            let write_end = base.checked_add(write.size as u64);
            let read_end = offset.checked_add(size as u64);
            if let (Some(write_end), Some(read_end)) = (write_end, read_end)
                && base <= offset
                && write_end >= read_end
            {
                let relative = offset - base;
                if relative == 0 && write.size == size {
                    return adjust_bits(ctx, &write.value, size * 8);
                }
                let low_bit = (relative * 8) as u32;
                let high_bit = low_bit + (size * 8) - 1;
                return adjust_bits(ctx, &write.value, write.size * 8)
                    .extract(ctx, high_bit, low_bit);
            }
        }

        let mut concrete_bytes = Vec::with_capacity(size as usize);
        let mut value = 0u64;
        let mut all_concrete = true;
        for index in 0..size {
            let byte_offset = offset.wrapping_add(index as u64);
            if let Some(byte) = self.concrete.get(&byte_offset) {
                concrete_bytes.push(*byte);
                if index < 8 {
                    value |= (*byte as u64) << (index * 8);
                }
            } else {
                all_concrete = false;
                break;
            }
        }

        if all_concrete {
            if size > 8 {
                let mut bytes = concrete_bytes.iter().rev();
                let first = bytes.next().copied().unwrap_or(0);
                let mut ast = BV::from_u64(first as u64, 8);
                for byte in bytes {
                    ast = ast.concat(BV::from_u64(*byte as u64, 8));
                }
                return SymValue::symbolic(ast, size * 8);
            }
            return SymValue::concrete(value, size * 8);
        }

        if default_symbolic {
            SymValue::new_symbolic(ctx, default_name, size * 8)
        } else {
            SymValue::concrete(0, size * 8)
        }
    }

    fn write_offset(&mut self, ctx: &'ctx Context, offset: u64, value: &SymValue<'ctx>, size: u32) {
        let bits = size * 8;
        let value = adjust_bits(ctx, value, bits);
        self.ensure_extent_covers(offset, size);
        if let Some(concrete_value) = value.as_concrete() {
            for index in 0..size {
                let byte_offset = offset.wrapping_add(index as u64);
                let byte_value = ((concrete_value >> (index * 8)) & 0xff) as u8;
                self.concrete.insert(byte_offset, byte_value);
            }
        }
        self.symbolic_writes.push(RegionWrite {
            target: RegionWriteTarget::Offset(offset),
            value,
            size,
        });
    }

    fn push_unresolved_write(&mut self, addr: SymValue<'ctx>, value: SymValue<'ctx>, size: u32) {
        self.symbolic_writes.push(RegionWrite {
            target: RegionWriteTarget::Address(addr),
            value,
            size,
        });
    }
}

/// A symbolic memory model backed by explicit regions.
pub struct SymMemory<'ctx> {
    ctx: &'ctx Context,
    regions: BTreeMap<MemoryRegionId, MemoryRegion<'ctx>>,
    default_symbolic: bool,
    max_symbolic_targets: usize,
    next_region_id: u32,
    escaped_unknown_region: MemoryRegionId,
}

impl<'ctx> SymMemory<'ctx> {
    const DEFAULT_MAX_SYMBOLIC_TARGETS: usize = 256;

    pub fn new(ctx: &'ctx Context) -> Self {
        Self::new_with_default(ctx, false)
    }

    pub fn new_symbolic(ctx: &'ctx Context) -> Self {
        Self::new_with_default(ctx, true)
    }

    fn new_with_default(ctx: &'ctx Context, default_symbolic: bool) -> Self {
        let escaped_unknown_region = MemoryRegionId(0);
        let mut regions = BTreeMap::new();
        regions.insert(
            escaped_unknown_region,
            MemoryRegion::new(
                escaped_unknown_region,
                MemoryRegionKind::EscapedUnknown,
                "escaped_unknown",
                None,
                None,
            ),
        );

        Self {
            ctx,
            regions,
            default_symbolic,
            max_symbolic_targets: Self::DEFAULT_MAX_SYMBOLIC_TARGETS,
            next_region_id: 1,
            escaped_unknown_region,
        }
    }

    pub fn set_max_symbolic_targets(&mut self, max: usize) {
        self.max_symbolic_targets = max;
    }

    pub fn escaped_unknown_region(&self) -> MemoryRegionId {
        self.escaped_unknown_region
    }

    pub fn define_region(
        &mut self,
        kind: MemoryRegionKind,
        name: impl Into<String>,
        base_addr: Option<u64>,
        extent: Option<u64>,
    ) -> MemoryRegionId {
        let name = name.into();
        if let Some(existing) = self.regions.values().find(|region| {
            region.def.kind == kind
                && region.def.name == name
                && region.def.base_addr == base_addr
                && region.def.extent == extent
        }) {
            return existing.def.id;
        }

        let id = MemoryRegionId(self.next_region_id);
        self.next_region_id += 1;
        self.regions
            .insert(id, MemoryRegion::new(id, kind, name, base_addr, extent));
        id
    }

    pub fn region_defs(&self) -> Vec<SymbolicMemoryRegionDef> {
        self.regions
            .values()
            .map(|region| region.def.clone())
            .collect()
    }

    pub fn region_def(&self, region_id: MemoryRegionId) -> Option<&SymbolicMemoryRegionDef> {
        self.regions.get(&region_id).map(|region| &region.def)
    }

    pub fn seed_region_bytes(&mut self, region_id: MemoryRegionId, offset: u64, bytes: &[u8]) {
        let Some(region) = self.regions.get_mut(&region_id) else {
            return;
        };
        region.ensure_extent_covers(offset, bytes.len() as u32);
        for (index, byte) in bytes.iter().copied().enumerate() {
            region.concrete.insert(offset + index as u64, byte);
        }
    }

    pub fn allocate_heap_region(
        &mut self,
        name: impl Into<String>,
        size: u64,
    ) -> (MemoryRegionId, u64) {
        let id = MemoryRegionId(self.next_region_id);
        let base_addr = 0x6000_0000u64 + (id.0 as u64) * 0x10000;
        let region_id = self.define_region(
            MemoryRegionKind::Heap,
            name.into(),
            Some(base_addr),
            Some(size),
        );
        (region_id, base_addr)
    }

    pub fn resolve_pointer(
        &self,
        addr: &SymValue<'ctx>,
        size: u32,
        constraints: &[Bool],
    ) -> ResolvedPointerSet {
        if let Some(concrete_addr) = addr.as_concrete()
            && let Some(pointer) = self.resolve_concrete_pointer(concrete_addr, addr.bits(), size)
        {
            return ResolvedPointerSet {
                pointers: vec![pointer],
                truncated: false,
            };
        }

        let (targets, truncated) = self.enumerate_symbolic_addresses(addr, constraints);
        let mut seen = BTreeSet::new();
        let mut pointers = Vec::new();
        for target in targets {
            if let Some(pointer) = self.resolve_concrete_pointer(target, addr.bits(), size)
                && seen.insert((pointer.region_id, pointer.offset))
            {
                pointers.push(pointer);
            }
        }

        ResolvedPointerSet {
            pointers,
            truncated,
        }
    }

    pub fn region_read(&self, pointer: &RegionPointer, size: u32) -> SymValue<'ctx> {
        self.read_region_pointer(pointer, size)
    }

    pub fn region_write(&mut self, pointer: &RegionPointer, value: &SymValue<'ctx>, size: u32) {
        self.write_region_pointer(pointer, value, size);
    }

    pub(crate) fn semantic_fingerprint(&self) -> String {
        let region_repr = self
            .regions
            .values()
            .map(|region| {
                let concrete = region
                    .concrete
                    .iter()
                    .map(|(offset, byte)| format!("{offset:x}:{byte:02x}"))
                    .collect::<Vec<_>>()
                    .join(",");
                let symbolic = region
                    .symbolic_writes
                    .iter()
                    .map(|write| {
                        let target = match &write.target {
                            RegionWriteTarget::Offset(offset) => format!("off:{offset:x}"),
                            RegionWriteTarget::Address(addr) => {
                                format!("addr:{}", addr.to_bv(self.ctx).simplify())
                            }
                        };
                        format!(
                            "{target}=>{}:{}",
                            write.value.to_bv(self.ctx).simplify(),
                            write.size
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("|");
                format!(
                    "{}:{:?}:{}:{:?}:{:?}:c[{}]:s[{}]",
                    region.def.id.0,
                    region.def.kind,
                    region.def.name,
                    region.def.base_addr,
                    region.def.extent,
                    concrete,
                    symbolic
                )
            })
            .collect::<Vec<_>>()
            .join(";");

        format!(
            "default_symbolic={};max_targets={};regions=[{}]",
            self.default_symbolic, self.max_symbolic_targets, region_repr
        )
    }

    pub(crate) fn merge_with(
        &self,
        other: &Self,
        constraints_self: &[Bool],
        constraints_other: &[Bool],
        cond_other: &Bool,
    ) -> Self {
        let mut merged = self.fork();
        let mut region_map = BTreeMap::new();

        for region in other.regions.values() {
            let target_id = if let Some(existing) = merged.regions.values().find(|existing| {
                existing.def.kind == region.def.kind
                    && existing.def.name == region.def.name
                    && existing.def.base_addr == region.def.base_addr
                    && existing.def.extent == region.def.extent
            }) {
                existing.def.id
            } else {
                merged.define_region(
                    region.def.kind.clone(),
                    region.def.name.clone(),
                    region.def.base_addr,
                    region.def.extent,
                )
            };
            region_map.insert(region.def.id, target_id);
        }

        let all_region_ids = merged.regions.keys().copied().collect::<Vec<_>>();
        for region_id in all_region_ids {
            let merged_def = match merged.region_def(region_id).cloned() {
                Some(def) => def,
                None => continue,
            };
            let other_region = region_map
                .iter()
                .find_map(|(other_id, mapped)| {
                    (*mapped == region_id).then(|| other.regions.get(other_id))
                })
                .flatten();
            let self_region = self
                .regions
                .values()
                .find(|region| region.def == merged_def);
            let mut offsets = BTreeSet::new();
            if let Some(region) = self_region {
                offsets.extend(region.merge_offsets());
            }
            if let Some(region) = other_region {
                offsets.extend(region.merge_offsets());
            }

            for offset in offsets {
                let pointer = RegionPointer {
                    region_id,
                    offset,
                    ptr_bits: 64,
                };
                let self_value = self_region
                    .map(|region| {
                        region.read_offset(
                            self.ctx,
                            offset,
                            1,
                            self.default_symbolic,
                            &format!("merge_self_{}_{}", region_id.0, offset),
                        )
                    })
                    .unwrap_or_else(|| self.default_byte(&pointer, 1));
                let other_value = other_region
                    .map(|region| {
                        region.read_offset(
                            self.ctx,
                            offset,
                            1,
                            other.default_symbolic,
                            &format!("merge_other_{}_{}", region_id.0, offset),
                        )
                    })
                    .unwrap_or_else(|| other.default_byte(&pointer, 1));
                let merged_value = merge_values(self.ctx, cond_other, &self_value, &other_value);
                merged.region_write(&pointer, &merged_value, 1);
            }
        }

        for region in other.regions.values() {
            let Some(mapped_region) = region_map.get(&region.def.id).copied() else {
                continue;
            };
            let Some(target) = merged.regions.get_mut(&mapped_region) else {
                continue;
            };
            for write in region.unresolved_symbolic_writes() {
                let RegionWriteTarget::Address(addr) = &write.target else {
                    continue;
                };
                target.push_unresolved_write(addr.clone(), write.value.clone(), write.size);
            }
        }

        let _ = constraints_self;
        let _ = constraints_other;
        merged
    }

    pub fn read(&self, addr: &SymValue<'ctx>, size: u32) -> SymValue<'ctx> {
        self.read_with_constraints(addr, size, &[])
    }

    pub fn read_with_constraints(
        &self,
        addr: &SymValue<'ctx>,
        size: u32,
        constraints: &[Bool],
    ) -> SymValue<'ctx> {
        let addr_taint = addr.get_taint();
        if let Some(concrete_addr) = addr.as_concrete() {
            return self
                .read_concrete(concrete_addr, addr.bits(), size)
                .with_taint(addr_taint);
        }

        let bits = size * 8;
        let mut result = if self.default_symbolic {
            SymValue::symbolic_tainted(BV::fresh_const("mem_sym", bits), bits, addr_taint)
        } else {
            SymValue::concrete_tainted(0, bits, addr_taint)
        };

        let resolved = self.resolve_pointer(addr, size, constraints);
        if resolved.pointers.is_empty() {
            return result;
        }

        let addr_bv = addr.to_bv(self.ctx);
        for pointer in resolved.pointers {
            let Some(def) = self.region_def(pointer.region_id) else {
                continue;
            };
            let Some(base_addr) = def.base_addr else {
                continue;
            };
            let target_addr = base_addr.wrapping_add(pointer.offset);
            let value = self.region_read(&pointer, size).with_taint(addr_taint);
            let cond = addr_bv.eq(BV::from_u64(target_addr, addr.bits()));
            let taint = value.get_taint() | result.get_taint();
            result = SymValue::symbolic_tainted(
                cond.ite(&value.to_bv(self.ctx), &result.to_bv(self.ctx)),
                bits,
                taint,
            );
        }

        result
    }

    pub fn write(&mut self, addr: &SymValue<'ctx>, value: &SymValue<'ctx>, size: u32) {
        self.write_with_constraints(addr, value, size, &[]);
    }

    pub fn write_with_constraints(
        &mut self,
        addr: &SymValue<'ctx>,
        value: &SymValue<'ctx>,
        size: u32,
        constraints: &[Bool],
    ) {
        let bits = size * 8;
        let value = adjust_bits(self.ctx, value, bits);

        if let Some(concrete_addr) = addr.as_concrete()
            && let Some(pointer) = self.resolve_concrete_pointer(concrete_addr, addr.bits(), size)
        {
            self.write_region_pointer(&pointer, &value, size);
            return;
        }

        let resolved = self.resolve_pointer(addr, size, constraints);
        if resolved.pointers.is_empty() {
            if let Some(region) = self.regions.get_mut(&self.escaped_unknown_region) {
                region.push_unresolved_write(addr.clone(), value, size);
            }
            return;
        }

        let addr_bv = addr.to_bv(self.ctx);
        for pointer in resolved.pointers {
            let existing = self.read_region_pointer(&pointer, size);
            let Some(def) = self.region_def(pointer.region_id) else {
                continue;
            };
            let Some(base_addr) = def.base_addr else {
                continue;
            };
            let concrete_target = base_addr.wrapping_add(pointer.offset);
            let cond = addr_bv.eq(BV::from_u64(concrete_target, addr.bits()));
            let taint = existing.get_taint() | value.get_taint() | addr.get_taint();
            let merged = SymValue::symbolic_tainted(
                cond.ite(&value.to_bv(self.ctx), &existing.to_bv(self.ctx)),
                bits,
                taint,
            );
            self.write_region_pointer(&pointer, &merged, size);
        }

        if resolved.truncated
            && let Some(region) = self.regions.get_mut(&self.escaped_unknown_region)
        {
            region.push_unresolved_write(addr.clone(), value, size);
        }
    }

    pub fn write_bytes(&mut self, addr: u64, bytes: &[u8]) {
        for (index, byte) in bytes.iter().copied().enumerate() {
            let addr = SymValue::concrete(addr + index as u64, 64);
            let value = SymValue::concrete(byte as u64, 8);
            self.write(&addr, &value, 1);
        }
    }

    pub fn read_bytes(&self, addr: u64, size: usize) -> Option<Vec<u8>> {
        let mut bytes = Vec::with_capacity(size);
        for index in 0..size {
            let pointer = self.resolve_concrete_pointer(addr + index as u64, 64, 1)?;
            let region = self.regions.get(&pointer.region_id)?;
            bytes.push(*region.concrete.get(&pointer.offset)?);
        }
        Some(bytes)
    }

    pub fn is_concrete_range(&self, addr: u64, size: u32) -> bool {
        for index in 0..size {
            let Some(pointer) = self.resolve_concrete_pointer(addr + index as u64, 64, 1) else {
                return false;
            };
            let Some(region) = self.regions.get(&pointer.region_id) else {
                return false;
            };
            if !region.concrete.contains_key(&pointer.offset) {
                return false;
            }
        }
        true
    }

    pub fn concrete_size(&self) -> usize {
        self.regions
            .values()
            .map(|region| region.concrete.len())
            .sum()
    }

    pub fn symbolic_writes_count(&self) -> usize {
        self.regions
            .values()
            .map(|region| region.symbolic_writes.len())
            .sum()
    }

    pub fn fork(&self) -> Self {
        Self {
            ctx: self.ctx,
            regions: self.regions.clone(),
            default_symbolic: self.default_symbolic,
            max_symbolic_targets: self.max_symbolic_targets,
            next_region_id: self.next_region_id,
            escaped_unknown_region: self.escaped_unknown_region,
        }
    }

    pub fn clear(&mut self) {
        for region in self.regions.values_mut() {
            region.concrete.clear();
            region.symbolic_writes.clear();
        }
    }

    fn resolve_concrete_pointer(
        &self,
        addr: u64,
        ptr_bits: u32,
        size: u32,
    ) -> Option<RegionPointer> {
        let region = self
            .regions
            .values()
            .filter(|region| region.contains_absolute_range(addr, size))
            .min_by(|left, right| compare_region_specificity(left, right))
            .map(|region| region.def.id)
            .unwrap_or(self.escaped_unknown_region);

        let offset = if region == self.escaped_unknown_region {
            addr
        } else {
            self.regions.get(&region)?.absolute_to_offset(addr)?
        };

        Some(RegionPointer {
            region_id: region,
            offset,
            ptr_bits,
        })
    }

    fn read_concrete(&self, addr: u64, ptr_bits: u32, size: u32) -> SymValue<'ctx> {
        let Some(pointer) = self.resolve_concrete_pointer(addr, ptr_bits, size) else {
            return SymValue::concrete(0, size * 8);
        };
        self.read_region_pointer(&pointer, size)
    }

    fn read_region_pointer(&self, pointer: &RegionPointer, size: u32) -> SymValue<'ctx> {
        let Some(region) = self.regions.get(&pointer.region_id) else {
            return self.default_byte(pointer, size);
        };
        region.read_offset(
            self.ctx,
            pointer.offset,
            size,
            self.default_symbolic,
            &format!("mem_{}_{}", pointer.region_id.0, pointer.offset),
        )
    }

    fn write_region_pointer(&mut self, pointer: &RegionPointer, value: &SymValue<'ctx>, size: u32) {
        let Some(region) = self.regions.get_mut(&pointer.region_id) else {
            return;
        };
        region.write_offset(self.ctx, pointer.offset, value, size);
    }

    fn default_byte(&self, pointer: &RegionPointer, size: u32) -> SymValue<'ctx> {
        if self.default_symbolic {
            SymValue::new_symbolic(
                self.ctx,
                &format!("mem_{}_{}", pointer.region_id.0, pointer.offset),
                size * 8,
            )
        } else {
            SymValue::concrete(0, size * 8)
        }
    }

    fn enumerate_symbolic_addresses(
        &self,
        addr: &SymValue<'ctx>,
        constraints: &[Bool],
    ) -> (Vec<u64>, bool) {
        if self.max_symbolic_targets == 0 {
            return (Vec::new(), true);
        }

        let solver = Solver::new();
        for constraint in constraints {
            solver.assert(constraint);
        }

        let addr_bv = addr.to_bv(self.ctx);
        let mut targets = Vec::new();
        let mut truncated = false;

        while targets.len() < self.max_symbolic_targets {
            if solver.check() != SatResult::Sat {
                break;
            }
            let Some(model) = solver.get_model() else {
                break;
            };
            let Some(value) = model.eval(&addr_bv, true).and_then(|value| value.as_u64()) else {
                truncated = true;
                break;
            };

            targets.push(value);
            solver.assert(addr_bv.eq(BV::from_u64(value, addr.bits())).not());
        }

        if targets.len() == self.max_symbolic_targets && solver.check() == SatResult::Sat {
            truncated = true;
        }

        (targets, truncated)
    }
}

fn compare_region_specificity<'ctx>(
    left: &MemoryRegion<'ctx>,
    right: &MemoryRegion<'ctx>,
) -> std::cmp::Ordering {
    let left_key = (
        left.def.extent.is_none(),
        left.def.extent.unwrap_or(u64::MAX),
        std::cmp::Reverse(left.def.base_addr.unwrap_or(0)),
        left.def.id,
    );
    let right_key = (
        right.def.extent.is_none(),
        right.def.extent.unwrap_or(u64::MAX),
        std::cmp::Reverse(right.def.base_addr.unwrap_or(0)),
        right.def.id,
    );
    left_key.cmp(&right_key)
}

fn merge_values<'ctx>(
    ctx: &'ctx Context,
    cond: &Bool,
    base: &SymValue<'ctx>,
    incoming: &SymValue<'ctx>,
) -> SymValue<'ctx> {
    let bits = base.bits().max(incoming.bits());
    let taint = base.get_taint() | incoming.get_taint();
    let base_bv = widen_value(ctx, base, bits);
    let incoming_bv = widen_value(ctx, incoming, bits);
    SymValue::symbolic_tainted(cond.ite(&incoming_bv, &base_bv), bits, taint)
}

fn widen_value<'ctx>(ctx: &'ctx Context, value: &SymValue<'ctx>, bits: u32) -> BV {
    let bv = value.to_bv(ctx);
    let value_bits = value.bits();
    if value_bits == bits {
        bv
    } else if value_bits < bits {
        bv.zero_ext(bits - value_bits)
    } else {
        bv.extract(bits - 1, 0)
    }
}

fn adjust_bits<'ctx>(ctx: &'ctx Context, value: &SymValue<'ctx>, bits: u32) -> SymValue<'ctx> {
    if value.bits() == bits {
        return value.clone();
    }
    if value.bits() < bits {
        value.zero_extend(ctx, bits)
    } else {
        value.extract(ctx, bits - 1, 0)
    }
}

impl<'ctx> std::fmt::Debug for SymMemory<'ctx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SymMemory")
            .field("regions", &self.regions.len())
            .field("concrete_bytes", &self.concrete_size())
            .field("symbolic_writes", &self.symbolic_writes_count())
            .field("default_symbolic", &self.default_symbolic)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use z3::ast::BV;
    use z3::{SatResult, Solver};

    #[test]
    fn test_concrete_read_write() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);
        let globals = mem.define_region(
            MemoryRegionKind::Global,
            "globals",
            Some(0x1000),
            Some(0x100),
        );

        let ptr = RegionPointer {
            region_id: globals,
            offset: 0,
            ptr_bits: 64,
        };
        mem.region_write(&ptr, &SymValue::concrete(0xdeadbeef, 32), 4);

        let addr = SymValue::concrete(0x1000, 64);
        assert_eq!(mem.read(&addr, 4).as_concrete(), Some(0xdeadbeef));
    }

    #[test]
    fn test_region_resolution_prefers_specific_input_over_stack() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);
        let _stack = mem.define_region(
            MemoryRegionKind::Stack,
            "stack_window",
            Some(0x7fff_0000 - 0x8000),
            Some(0x10000),
        );
        let input = mem.define_region(
            MemoryRegionKind::Input,
            "stdin",
            Some(0x7fff_1000),
            Some(0x10),
        );

        let resolved = mem.resolve_pointer(&SymValue::concrete(0x7fff_1004, 64), 1, &[]);
        assert_eq!(resolved.pointers.len(), 1);
        assert_eq!(resolved.pointers[0].region_id, input);
        assert_eq!(resolved.pointers[0].offset, 4);
    }

    #[test]
    fn test_symbolic_address_write_then_read() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);
        mem.define_region(
            MemoryRegionKind::Global,
            "globals",
            Some(0x1000),
            Some(0x2000),
        );

        let idx = SymValue::new_symbolic(&ctx, "idx", 64);
        let addr_bv = idx.to_bv(&ctx);
        let eq1 = addr_bv.eq(BV::from_u64(0x1000, 64));
        let eq2 = addr_bv.eq(BV::from_u64(0x2000, 64));
        let constraint = eq1.clone() | eq2.clone();

        let value = SymValue::concrete(0xcafebabe, 32);
        mem.write_with_constraints(&idx, &value, 4, std::slice::from_ref(&constraint));

        let read_value = mem.read_with_constraints(&idx, 4, &[constraint]);
        assert!(read_value.is_symbolic());

        let solver = Solver::new();
        solver.assert(&eq1);
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let value = model
            .eval(&read_value.to_bv(&ctx), true)
            .unwrap()
            .as_u64()
            .unwrap();
        assert_eq!(value, 0xcafebabe);

        let solver = Solver::new();
        solver.assert(&eq2);
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let value = model
            .eval(&read_value.to_bv(&ctx), true)
            .unwrap()
            .as_u64()
            .unwrap();
        assert_eq!(value, 0xcafebabe);
    }

    #[test]
    fn test_unknown_region_preserves_concrete_bytes() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);
        mem.write_bytes(0x9000, &[0x11, 0x22, 0x33, 0x44]);
        assert_eq!(
            mem.read_bytes(0x9000, 4),
            Some(vec![0x11, 0x22, 0x33, 0x44])
        );
    }
}
