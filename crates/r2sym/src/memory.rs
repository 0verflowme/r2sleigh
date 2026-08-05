//! Symbolic memory model for symbolic execution.
//!
//! The memory core is region-based: concrete and symbolic bytes live under
//! explicit stack/global/input/heap/replay/unknown regions. The public API
//! remains address-shaped for compatibility with the executor and summaries.

use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use serde::{Deserialize, Serialize};
use z3::ast::{Ast, BV, Bool};
use z3::{Context, DeclKind, SatResult, Solver};

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
struct RegionOffsetWrite<'ctx> {
    offset: u64,
    value: SymValue<'ctx>,
    size: u32,
}

#[derive(Clone)]
struct RegionUnresolvedWrite<'ctx> {
    addr: SymValue<'ctx>,
    value: SymValue<'ctx>,
    size: u32,
}

#[derive(Clone)]
struct MemoryRegion<'ctx> {
    def: SymbolicMemoryRegionDef,
    concrete: BTreeMap<u64, u8>,
    offset_writes: Vec<RegionOffsetWrite<'ctx>>,
    latest_write_by_offset: BTreeMap<u64, usize>,
    unresolved_writes: Vec<RegionUnresolvedWrite<'ctx>>,
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
            offset_writes: Vec::new(),
            latest_write_by_offset: BTreeMap::new(),
            unresolved_writes: Vec::new(),
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
        offsets.extend(self.latest_write_by_offset.keys().copied());
        offsets
    }

    fn unresolved_symbolic_writes(&self) -> impl Iterator<Item = &RegionUnresolvedWrite<'ctx>> {
        self.unresolved_writes.iter()
    }

    fn read_byte_from_offset_write(
        &self,
        ctx: &'ctx Context,
        byte_offset: u64,
    ) -> Option<SymValue<'ctx>> {
        let write_index = *self.latest_write_by_offset.get(&byte_offset)?;
        let write = self.offset_writes.get(write_index)?;
        let relative = byte_offset.checked_sub(write.offset)?;
        if relative >= write.size as u64 {
            return None;
        }
        let value = adjust_bits(ctx, &write.value, write.size * 8);
        let low_bit = (relative * 8) as u32;
        let high_bit = low_bit + 7;
        Some(value.extract(ctx, high_bit, low_bit))
    }

    fn default_read_byte(
        &self,
        ctx: &'ctx Context,
        byte_offset: u64,
        default_symbolic: bool,
        default_name: &str,
    ) -> SymValue<'ctx> {
        if let Some(byte) = self.read_byte_from_offset_write(ctx, byte_offset) {
            return byte;
        }
        if let Some(byte) = self.concrete.get(&byte_offset) {
            return SymValue::concrete(*byte as u64, 8);
        }
        if default_symbolic {
            SymValue::new_symbolic(ctx, &format!("{default_name}_b{byte_offset:x}"), 8)
        } else {
            SymValue::concrete(0, 8)
        }
    }

    fn read_offset(
        &self,
        ctx: &'ctx Context,
        offset: u64,
        size: u32,
        default_symbolic: bool,
        default_name: &str,
    ) -> SymValue<'ctx> {
        let mut byte_values = Vec::with_capacity(size as usize);
        let mut value = 0u64;
        let mut all_concrete = true;
        for index in 0..size {
            let byte_offset = offset.wrapping_add(index as u64);
            let byte = self.default_read_byte(ctx, byte_offset, default_symbolic, default_name);
            if let Some(concrete) = byte.as_concrete() {
                if index < 8 {
                    value |= concrete << (index * 8);
                }
            } else {
                all_concrete = false;
            }
            byte_values.push(byte);
        }

        if all_concrete {
            if size > 8 {
                let mut bytes = byte_values.iter().rev().filter_map(SymValue::as_concrete);
                let first = bytes.next().unwrap_or(0);
                let mut ast = BV::from_u64(first, 8);
                for byte in bytes {
                    ast = ast.concat(BV::from_u64(byte, 8));
                }
                return SymValue::symbolic(ast, size * 8);
            }
            return SymValue::concrete(value, size * 8);
        }

        let mut bytes = byte_values.iter().rev();
        let Some(first) = bytes.next() else {
            return if default_symbolic {
                SymValue::new_symbolic(ctx, default_name, size * 8)
            } else {
                SymValue::concrete(0, size * 8)
            };
        };
        let mut ast = first.to_bv(ctx);
        let mut taint = first.get_taint();
        for byte in bytes {
            ast = ast.concat(byte.to_bv(ctx));
            taint |= byte.get_taint();
        }
        SymValue::symbolic_tainted(ast, size * 8, taint)
    }

    fn write_offset(&mut self, ctx: &'ctx Context, offset: u64, value: &SymValue<'ctx>, size: u32) {
        let bits = size * 8;
        let value = adjust_bits(ctx, value, bits);
        self.ensure_extent_covers(offset, size);
        if let Some(concrete_value) = value.as_concrete() {
            for index in 0..size {
                let byte_offset = offset.wrapping_add(index as u64);
                let byte_value = if index < 8 {
                    ((concrete_value >> (index * 8)) & 0xff) as u8
                } else {
                    0
                };
                self.concrete.insert(byte_offset, byte_value);
            }
        } else {
            for index in 0..size {
                self.concrete.remove(&offset.wrapping_add(index as u64));
            }
        }
        let write_index = self.offset_writes.len();
        self.offset_writes.push(RegionOffsetWrite {
            offset,
            value,
            size,
        });
        for index in 0..size {
            self.latest_write_by_offset
                .insert(offset.wrapping_add(index as u64), write_index);
        }
    }

    fn push_unresolved_write(&mut self, addr: SymValue<'ctx>, value: SymValue<'ctx>, size: u32) {
        self.unresolved_writes
            .push(RegionUnresolvedWrite { addr, value, size });
    }

    fn visible_offset_write_indices(&self) -> Vec<usize> {
        let mut indices = self
            .latest_write_by_offset
            .values()
            .copied()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        indices.sort_unstable();
        indices
    }
}

/// A symbolic memory model backed by explicit regions.
pub struct SymMemory<'ctx> {
    ctx: &'ctx Context,
    regions: Rc<BTreeMap<MemoryRegionId, MemoryRegion<'ctx>>>,
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
            regions: Rc::new(regions),
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
        Rc::make_mut(&mut self.regions)
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
        let Some(region) = Rc::make_mut(&mut self.regions).get_mut(&region_id) else {
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

        let (targets, truncated) = self.enumerate_symbolic_addresses(addr, size, constraints);
        let mut seen = BTreeSet::new();
        let mut pointers = Vec::new();
        let mut escaped_unknown = false;
        for target in targets {
            if let Some(pointer) = self.resolve_concrete_pointer(target, addr.bits(), size) {
                if pointer.region_id == self.escaped_unknown_region {
                    escaped_unknown = true;
                    continue;
                }
                if !seen.insert((pointer.region_id, pointer.offset)) {
                    continue;
                }
                pointers.push(pointer);
            }
        }

        ResolvedPointerSet {
            pointers,
            truncated: truncated || escaped_unknown,
        }
    }

    pub fn region_read(&self, pointer: &RegionPointer, size: u32) -> SymValue<'ctx> {
        self.read_region_pointer(pointer, size)
    }

    pub fn region_write(&mut self, pointer: &RegionPointer, value: &SymValue<'ctx>, size: u32) {
        self.write_region_pointer(pointer, value, size);
    }

    pub(crate) fn semantic_fingerprint(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.default_symbolic.hash(&mut hasher);
        self.max_symbolic_targets.hash(&mut hasher);
        self.next_region_id.hash(&mut hasher);
        self.escaped_unknown_region.hash(&mut hasher);

        for region in self.regions.values() {
            region.def.id.hash(&mut hasher);
            region.def.kind.hash(&mut hasher);
            region.def.name.hash(&mut hasher);
            region.def.base_addr.hash(&mut hasher);
            region.def.extent.hash(&mut hasher);

            for (offset, byte) in &region.concrete {
                offset.hash(&mut hasher);
                byte.hash(&mut hasher);
            }

            for index in region.visible_offset_write_indices() {
                if let Some(write) = region.offset_writes.get(index) {
                    if write.value.as_concrete().is_some() {
                        continue;
                    }
                    write.offset.hash(&mut hasher);
                    write.size.hash(&mut hasher);
                    hash_sym_value(self.ctx, &write.value, &mut hasher);
                }
            }

            for write in &region.unresolved_writes {
                write.size.hash(&mut hasher);
                hash_sym_value(self.ctx, &write.addr, &mut hasher);
                hash_sym_value(self.ctx, &write.value, &mut hasher);
            }
        }

        hasher.finish()
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
            let Some(target) = Rc::make_mut(&mut merged.regions).get_mut(&mapped_region) else {
                continue;
            };
            for write in region.unresolved_symbolic_writes() {
                target.push_unresolved_write(write.addr.clone(), write.value.clone(), write.size);
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
            if let Some(region) =
                Rc::make_mut(&mut self.regions).get_mut(&self.escaped_unknown_region)
            {
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
            && let Some(region) =
                Rc::make_mut(&mut self.regions).get_mut(&self.escaped_unknown_region)
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
            .map(|region| region.offset_writes.len() + region.unresolved_writes.len())
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
        for region in Rc::make_mut(&mut self.regions).values_mut() {
            region.concrete.clear();
            region.offset_writes.clear();
            region.latest_write_by_offset.clear();
            region.unresolved_writes.clear();
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
        let Some(region) = Rc::make_mut(&mut self.regions).get_mut(&pointer.region_id) else {
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
        size: u32,
        constraints: &[Bool],
    ) -> (Vec<u64>, bool) {
        if constraints.is_empty() {
            return finite_unconstrained_addresses(addr, self.max_symbolic_targets)
                .map(|targets| (targets, false))
                .unwrap_or_else(|| (Vec::new(), true));
        }
        self.enumerate_symbolic_addresses_sat(addr, size, constraints)
    }

    fn enumerate_symbolic_addresses_sat(
        &self,
        addr: &SymValue<'ctx>,
        size: u32,
        constraints: &[Bool],
    ) -> (Vec<u64>, bool) {
        if self.max_symbolic_targets == 0 {
            return (Vec::new(), true);
        }

        let addr_bv = addr.to_bv(self.ctx);
        if !constraints_reference_value(&addr_bv, constraints) {
            return (Vec::new(), true);
        }
        let Some(region_membership) = self.explicit_region_membership(&addr_bv, size) else {
            return (Vec::new(), true);
        };

        let solver = Solver::new();
        for constraint in constraints {
            solver.assert(constraint);
        }
        solver.assert(&region_membership);

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

        let outside_solver = Solver::new();
        for constraint in constraints {
            outside_solver.assert(constraint);
        }
        outside_solver.assert(region_membership.not());
        if outside_solver.check() != SatResult::Unsat {
            truncated = true;
        }

        (targets, truncated)
    }

    fn explicit_region_membership(&self, addr: &BV, size: u32) -> Option<Bool> {
        let bits = addr.get_size();
        if bits > 64 {
            return None;
        }
        let max_addr = if bits == 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        };
        let mut ranges = self.regions.values().filter_map(|region| {
            if region.def.kind == MemoryRegionKind::EscapedUnknown {
                return None;
            }
            let base = region.def.base_addr?;
            let extent = region.def.extent?;
            let max_start = base.checked_add(extent.checked_sub(u64::from(size))?)?;
            if base > max_addr || max_start > max_addr {
                return None;
            }
            let lower = addr.bvuge(BV::from_u64(base, bits));
            let upper = addr.bvule(BV::from_u64(max_start, bits));
            Some(lower & upper)
        });
        let first = ranges.next()?;
        Some(ranges.fold(first, |combined, range| combined | range))
    }
}

fn compare_region_specificity<'ctx>(
    left: &MemoryRegion<'ctx>,
    right: &MemoryRegion<'ctx>,
) -> std::cmp::Ordering {
    fn kind_rank(kind: &MemoryRegionKind) -> u8 {
        match kind {
            MemoryRegionKind::Replay => 0,
            MemoryRegionKind::Input => 1,
            MemoryRegionKind::Global => 2,
            MemoryRegionKind::Heap => 3,
            MemoryRegionKind::Stack => 4,
            MemoryRegionKind::EscapedUnknown => 5,
        }
    }

    let left_key = (
        left.def.extent.is_none(),
        left.def.extent.unwrap_or(u64::MAX),
        kind_rank(&left.def.kind),
        std::cmp::Reverse(left.def.base_addr.unwrap_or(0)),
        left.def.id,
    );
    let right_key = (
        right.def.extent.is_none(),
        right.def.extent.unwrap_or(u64::MAX),
        kind_rank(&right.def.kind),
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

fn hash_sym_value<'ctx, H: Hasher>(ctx: &'ctx Context, value: &SymValue<'ctx>, hasher: &mut H) {
    value.bits().hash(hasher);
    value.get_taint().hash(hasher);
    value.to_bv(ctx).hash(hasher);
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

fn finite_unconstrained_addresses<'ctx>(addr: &SymValue<'ctx>, limit: usize) -> Option<Vec<u64>> {
    if limit == 0 {
        return None;
    }
    let values = finite_bv_values(addr.as_ast()?, limit)?;
    Some(values.into_iter().collect())
}

fn finite_bv_values(ast: &BV, limit: usize) -> Option<BTreeSet<u64>> {
    if let Some(value) = ast.as_u64() {
        return Some(BTreeSet::from([value]));
    }
    let children = ast.children();
    match ast.decl().kind() {
        DeclKind::Ite if children.len() == 3 => {
            let mut values = finite_bv_values(&children[1].as_bv()?, limit)?;
            values.extend(finite_bv_values(&children[2].as_bv()?, limit)?);
            (values.len() <= limit).then_some(values)
        }
        DeclKind::Badd | DeclKind::Bsub if children.len() == 2 => {
            let left = finite_bv_values(&children[0].as_bv()?, limit)?;
            let right = finite_bv_values(&children[1].as_bv()?, limit)?;
            let bits = ast.get_size();
            let mask = if bits >= 64 {
                u64::MAX
            } else {
                (1u64 << bits) - 1
            };
            let mut values = BTreeSet::new();
            for lhs in left {
                for rhs in &right {
                    let value = if ast.decl().kind() == DeclKind::Badd {
                        lhs.wrapping_add(*rhs)
                    } else {
                        lhs.wrapping_sub(*rhs)
                    } & mask;
                    values.insert(value);
                    if values.len() > limit {
                        return None;
                    }
                }
            }
            Some(values)
        }
        _ => None,
    }
}

fn constraints_reference_value(value: &BV, constraints: &[Bool]) -> bool {
    let mut value_symbols = BTreeSet::new();
    collect_uninterpreted_symbols(value, &mut value_symbols);
    if value_symbols.is_empty() {
        return true;
    }
    constraints.iter().any(|constraint| {
        let mut constraint_symbols = BTreeSet::new();
        collect_uninterpreted_symbols(constraint, &mut constraint_symbols);
        !value_symbols.is_disjoint(&constraint_symbols)
    })
}

fn collect_uninterpreted_symbols(ast: &dyn Ast, symbols: &mut BTreeSet<String>) {
    let children = ast.children();
    if children.is_empty() {
        if ast.decl().kind() == DeclKind::Uninterpreted {
            symbols.insert(ast.decl().name());
        }
        return;
    }
    for child in children {
        collect_uninterpreted_symbols(&child, symbols);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use z3::ast::{BV, Bool};
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
    fn test_region_resolution_prefers_replay_over_global_when_overlapping() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);
        let global = mem.define_region(
            MemoryRegionKind::Global,
            "globals",
            Some(0x4000),
            Some(0x20),
        );
        let replay = mem.define_region(
            MemoryRegionKind::Replay,
            "checkpoint",
            Some(0x4000),
            Some(0x20),
        );

        let resolved = mem.resolve_pointer(&SymValue::concrete(0x4004, 64), 1, &[]);
        assert_eq!(resolved.pointers.len(), 1);
        assert_eq!(resolved.pointers[0].region_id, replay);
        assert_ne!(resolved.pointers[0].region_id, global);
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

    #[test]
    fn test_overlapping_concrete_offset_writes_preserve_exact_bytes() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);
        let globals = mem.define_region(
            MemoryRegionKind::Global,
            "globals",
            Some(0x2000),
            Some(0x100),
        );

        let base = RegionPointer {
            region_id: globals,
            offset: 0,
            ptr_bits: 64,
        };
        let overlap = RegionPointer {
            region_id: globals,
            offset: 1,
            ptr_bits: 64,
        };
        mem.region_write(&base, &SymValue::concrete(0x1122_3344, 32), 4);
        mem.region_write(&overlap, &SymValue::concrete(0xaabb, 16), 2);

        let addr = SymValue::concrete(0x2000, 64);
        assert_eq!(mem.read(&addr, 4).as_concrete(), Some(0x11aa_bb44));
        assert_eq!(
            mem.read_bytes(0x2000, 4),
            Some(vec![0x44, 0xbb, 0xaa, 0x11])
        );
    }

    #[test]
    fn test_symbolic_offset_write_invalidates_overwritten_concrete_bytes() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);
        let globals = mem.define_region(
            MemoryRegionKind::Global,
            "globals",
            Some(0x3000),
            Some(0x100),
        );
        mem.seed_region_bytes(globals, 0, &[0x10, 0x20, 0x30, 0x40]);

        let ptr = RegionPointer {
            region_id: globals,
            offset: 1,
            ptr_bits: 64,
        };
        mem.region_write(&ptr, &SymValue::new_symbolic(&ctx, "sym_word", 16), 2);

        assert_eq!(mem.read_bytes(0x3000, 4), None);
        assert!(!mem.is_concrete_range(0x3000, 4));
        assert_eq!(
            mem.read(&SymValue::concrete(0x3000, 64), 1).as_concrete(),
            Some(0x10)
        );
        assert!(mem.read(&SymValue::concrete(0x3001, 64), 1).is_symbolic());
        assert!(mem.read(&SymValue::concrete(0x3002, 64), 1).is_symbolic());
        assert_eq!(
            mem.read(&SymValue::concrete(0x3003, 64), 1).as_concrete(),
            Some(0x40)
        );
    }

    #[test]
    fn test_overlapping_symbolic_offset_writes_compose_by_byte() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);
        let globals = mem.define_region(
            MemoryRegionKind::Global,
            "globals",
            Some(0x4000),
            Some(0x100),
        );

        let wide = RegionPointer {
            region_id: globals,
            offset: 0,
            ptr_bits: 64,
        };
        let byte = RegionPointer {
            region_id: globals,
            offset: 1,
            ptr_bits: 64,
        };
        let word = SymValue::new_symbolic(&ctx, "word", 32);
        mem.region_write(&wide, &word, 4);
        mem.region_write(&byte, &SymValue::concrete(0xaa, 8), 1);

        let read_back = mem.read(&SymValue::concrete(0x4000, 64), 4);
        let solver = Solver::new();
        solver.assert(word.to_bv(&ctx).eq(BV::from_u64(0x1122_3344, 32)));
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let value = model
            .eval(&read_back.to_bv(&ctx), true)
            .and_then(|value| value.as_u64())
            .unwrap();
        assert_eq!(value, 0x1122_aa44);
    }

    #[test]
    fn test_wide_concrete_region_write_does_not_shift_overflow() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);
        let globals = mem.define_region(
            MemoryRegionKind::Global,
            "globals",
            Some(0x5000),
            Some(0x100),
        );

        let ptr = RegionPointer {
            region_id: globals,
            offset: 0,
            ptr_bits: 64,
        };
        mem.region_write(&ptr, &SymValue::concrete(0x1122_3344_5566_7788, 128), 16);

        assert_eq!(
            mem.read_bytes(0x5000, 16),
            Some(vec![
                0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0, 0, 0, 0, 0, 0, 0, 0,
            ])
        );
    }

    #[test]
    fn test_unconstrained_symbolic_pointer_stays_residual() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);
        mem.define_region(
            MemoryRegionKind::Global,
            "globals",
            Some(0x1000),
            Some(0x100),
        );
        let addr = SymValue::new_symbolic(&ctx, "unconstrained_ptr", 64);

        let resolved = mem.resolve_pointer(&addr, 4, &[]);

        assert!(resolved.pointers.is_empty());
        assert!(resolved.truncated);
    }

    #[test]
    fn test_finite_symbolic_pointer_choices_resolve_without_constraints() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);
        let globals = mem.define_region(
            MemoryRegionKind::Global,
            "globals",
            Some(0x1000),
            Some(0x100),
        );
        let choice = Bool::new_const("pointer_choice");
        let addr = SymValue::symbolic(
            choice.ite(&BV::from_u64(0x1004, 64), &BV::from_u64(0x1008, 64)),
            64,
        );

        let resolved = mem.resolve_pointer(&addr, 4, &[]);

        assert_eq!(resolved.pointers.len(), 2);
        assert!(
            resolved
                .pointers
                .iter()
                .all(|pointer| pointer.region_id == globals)
        );
        assert_eq!(
            resolved
                .pointers
                .iter()
                .map(|pointer| pointer.offset)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([4, 8])
        );
        assert!(!resolved.truncated);
    }

    #[test]
    fn test_region_directed_resolution_marks_unknown_space_residual() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);
        let globals = mem.define_region(
            MemoryRegionKind::Global,
            "globals",
            Some(0x1000),
            Some(0x100),
        );
        let addr = SymValue::new_symbolic(&ctx, "maybe_global", 64);
        let addr_bv = addr.to_bv(&ctx);
        let constraint =
            addr_bv.eq(BV::from_u64(0x1004, 64)) | addr_bv.eq(BV::from_u64(0x9000, 64));

        let resolved = mem.resolve_pointer(&addr, 4, &[constraint]);

        assert_eq!(resolved.pointers.len(), 1);
        assert_eq!(resolved.pointers[0].region_id, globals);
        assert_eq!(resolved.pointers[0].offset, 4);
        assert!(resolved.truncated);
    }

    #[test]
    fn test_semantic_fingerprint_ignores_equivalent_concrete_write_chunking() {
        let ctx = Context::thread_local();
        let mut lhs = SymMemory::new(&ctx);
        let mut rhs = SymMemory::new(&ctx);
        let globals_lhs = lhs.define_region(
            MemoryRegionKind::Global,
            "globals",
            Some(0x5000),
            Some(0x100),
        );
        let globals_rhs = rhs.define_region(
            MemoryRegionKind::Global,
            "globals",
            Some(0x5000),
            Some(0x100),
        );

        lhs.region_write(
            &RegionPointer {
                region_id: globals_lhs,
                offset: 0,
                ptr_bits: 64,
            },
            &SymValue::concrete(0x4433_2211, 32),
            4,
        );
        for (index, byte) in [0x11u8, 0x22, 0x33, 0x44].into_iter().enumerate() {
            rhs.region_write(
                &RegionPointer {
                    region_id: globals_rhs,
                    offset: index as u64,
                    ptr_bits: 64,
                },
                &SymValue::concrete(byte as u64, 8),
                1,
            );
        }

        assert_eq!(lhs.read_bytes(0x5000, 4), rhs.read_bytes(0x5000, 4));
        assert_eq!(lhs.semantic_fingerprint(), rhs.semantic_fingerprint());
    }
}
