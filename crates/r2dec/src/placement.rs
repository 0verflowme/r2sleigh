//! Pure declaration-placement and reaching-definition analysis.
//!
//! The sealed structured-region tree owns lexical ancestry. The canonical SSA
//! function owns CFG predecessors and dominance. This module joins those facts
//! with the read and write occurrences that survived final AST rewriting, then
//! returns an ephemeral decision. It deliberately retains neither a placement
//! table nor a dominance proof beside the tree that produced the answer.
//!
//! The region walk and occurrence grouping are linear. Must-assignment is a
//! forward bitset analysis over a sorted worklist, with cost
//! `O((bindings / word_bits) * (blocks + edges))` per fixpoint sweep.

#![allow(
    dead_code,
    reason = "Stage 7 placement analysis lands before final AST occurrence wiring"
)]

use std::collections::{BTreeMap, BTreeSet};

use crate::binding_plan::{BindingId, PlacementRefusal};
use crate::structured_region::{RegionId, SealedStructuredRegionArtifact};
use r2ssa::{InstId, SSAFunction, UseSite};

/// Final render-order position of an occurrence after every AST rewrite.
///
/// The final marker walk assigns this monotonically. Equal positions are
/// permitted for one expression: reads are evaluated before its write.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct FinalOccurrenceOrder(pub(crate) u64);

/// One binding read that survived all AST rewriting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FinalBindingRead {
    pub(crate) binding: BindingId,
    pub(crate) site: UseSite,
    pub(crate) region: RegionId,
    pub(crate) block: u64,
    pub(crate) order: FinalOccurrenceOrder,
}

/// One binding write that survived all AST rewriting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FinalBindingWrite {
    pub(crate) binding: BindingId,
    pub(crate) inst: InstId,
    pub(crate) region: RegionId,
    pub(crate) block: u64,
    pub(crate) order: FinalOccurrenceOrder,
}

/// A decision consumed immediately by final emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlacementDecision {
    /// Declare at the start of the lowest valid lexical region, then assign at
    /// each surviving write occurrence.
    LexicalDeclaration { region: RegionId },
    /// Replace the sole dominating assignment with a declaration initializer.
    Inline { write: InstId },
    /// Honest C cannot be emitted for this binding.
    Refused(PlacementRefusal),
}

/// Dense result in ascending `BindingId` order.
///
/// `None` means that the binding has no surviving occurrence and needs no C
/// declaration. The vector is transient and is not retained by `BindingPlan`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PlacementDecisions {
    decisions: Box<[Option<PlacementDecision>]>,
}

impl PlacementDecisions {
    pub(crate) fn decision(&self, binding: BindingId) -> Option<PlacementDecision> {
        self.decisions.get(binding.index()).copied().flatten()
    }
}

/// Structural mismatch between final occurrences and their two authorities.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlacementAnalysisError {
    BindingOutsidePlan { binding: BindingId },
    RegionOutsideArtifact { region: RegionId },
    BlockOutsideFunction { block: u64 },
    RegionDoesNotDominateOccurrence { region: RegionId, block: u64 },
}

/// Derive all declaration decisions from canonical facts and final occurrences.
pub(crate) fn derive_placement_decisions(
    regions: &SealedStructuredRegionArtifact,
    function: &SSAFunction,
    binding_count: usize,
    reads: &[FinalBindingRead],
    writes: &[FinalBindingWrite],
) -> Result<PlacementDecisions, PlacementAnalysisError> {
    derive_with_cfg(regions, function, binding_count, reads, writes)
}

trait PlacementControlFlow {
    fn entry(&self) -> u64;
    fn block_addrs(&self) -> Vec<u64>;
    fn predecessors(&self, block: u64) -> Vec<u64>;
    fn successors(&self, block: u64) -> Vec<u64>;
    fn dominates(&self, dominator: u64, block: u64) -> bool;
}

impl PlacementControlFlow for SSAFunction {
    fn entry(&self) -> u64 {
        self.entry
    }

    fn block_addrs(&self) -> Vec<u64> {
        SSAFunction::block_addrs(self).to_vec()
    }

    fn predecessors(&self, block: u64) -> Vec<u64> {
        SSAFunction::predecessors(self, block)
    }

    fn successors(&self, block: u64) -> Vec<u64> {
        SSAFunction::successors(self, block)
    }

    fn dominates(&self, dominator: u64, block: u64) -> bool {
        SSAFunction::dominates(self, dominator, block)
    }
}

fn derive_with_cfg<C: PlacementControlFlow + ?Sized>(
    regions: &SealedStructuredRegionArtifact,
    cfg: &C,
    binding_count: usize,
    reads: &[FinalBindingRead],
    writes: &[FinalBindingWrite],
) -> Result<PlacementDecisions, PlacementAnalysisError> {
    let mut block_addrs = cfg.block_addrs();
    block_addrs.sort_unstable();
    block_addrs.dedup();
    let block_indices = block_addrs
        .iter()
        .copied()
        .enumerate()
        .map(|(index, block)| (block, index))
        .collect::<BTreeMap<_, _>>();

    for read in reads {
        validate_occurrence(
            regions,
            cfg,
            binding_count,
            &block_indices,
            read.binding,
            read.region,
            read.block,
        )?;
    }
    for write in writes {
        validate_occurrence(
            regions,
            cfg,
            binding_count,
            &block_indices,
            write.binding,
            write.region,
            write.block,
        )?;
    }

    let mut occurrences = vec![Vec::<Occurrence>::new(); binding_count];
    for read in reads {
        occurrences[read.binding.index()].push(Occurrence {
            region: read.region,
            block: read.block,
            order: read.order,
            kind: OccurrenceKind::Read(read.site),
        });
    }
    for write in writes {
        occurrences[write.binding.index()].push(Occurrence {
            region: write.region,
            block: write.block,
            order: write.order,
            kind: OccurrenceKind::Write(write.inst),
        });
    }
    for binding_occurrences in &mut occurrences {
        binding_occurrences.sort_by_key(Occurrence::sort_key);
    }

    let must_in = must_assignment_inputs(
        cfg,
        binding_count,
        &block_addrs,
        &block_indices,
        &occurrences,
    );
    let mut decisions = vec![None; binding_count];

    for (binding_index, binding_occurrences) in occurrences.iter().enumerate() {
        if binding_occurrences.is_empty() {
            continue;
        }
        let binding = BindingId::from_dense_index(binding_index)
            .expect("binding_count is already addressable by BindingId occurrences");
        let writes_for_binding = binding_occurrences
            .iter()
            .filter_map(|occurrence| match occurrence.kind {
                OccurrenceKind::Write(inst) => Some((occurrence, inst)),
                OccurrenceKind::Read(_) => None,
            })
            .collect::<Vec<_>>();
        if writes_for_binding.is_empty() {
            decisions[binding_index] = Some(PlacementDecision::Refused(
                PlacementRefusal::MissingDefinition { binding },
            ));
            continue;
        }

        if let Some(site) =
            first_read_before_assignment(binding, binding_occurrences, &must_in, &block_indices)
        {
            decisions[binding_index] = Some(PlacementDecision::Refused(
                PlacementRefusal::ReadBeforeAssignment { binding, site },
            ));
            continue;
        }

        let Some(region) = lowest_dominating_region(regions, cfg, binding_occurrences) else {
            decisions[binding_index] = Some(PlacementDecision::Refused(
                PlacementRefusal::NoDominatingRegion { binding },
            ));
            continue;
        };

        if let [(write, inst)] = writes_for_binding.as_slice()
            && binding_occurrences.iter().all(|occurrence| {
                matches!(occurrence.kind, OccurrenceKind::Write(_))
                    || (write.order <= occurrence.order
                        && cfg.dominates(write.block, occurrence.block))
            })
        {
            decisions[binding_index] = Some(PlacementDecision::Inline { write: *inst });
        } else {
            decisions[binding_index] = Some(PlacementDecision::LexicalDeclaration { region });
        }
    }

    Ok(PlacementDecisions {
        decisions: decisions.into_boxed_slice(),
    })
}

fn validate_occurrence<C: PlacementControlFlow + ?Sized>(
    regions: &SealedStructuredRegionArtifact,
    cfg: &C,
    binding_count: usize,
    block_indices: &BTreeMap<u64, usize>,
    binding: BindingId,
    region: RegionId,
    block: u64,
) -> Result<(), PlacementAnalysisError> {
    if binding.index() >= binding_count {
        return Err(PlacementAnalysisError::BindingOutsidePlan { binding });
    }
    let Some(node) = regions.node(region) else {
        return Err(PlacementAnalysisError::RegionOutsideArtifact { region });
    };
    if !block_indices.contains_key(&block) {
        return Err(PlacementAnalysisError::BlockOutsideFunction { block });
    }
    if !cfg.dominates(node.entry(), block) {
        return Err(PlacementAnalysisError::RegionDoesNotDominateOccurrence { region, block });
    }
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Occurrence {
    region: RegionId,
    block: u64,
    order: FinalOccurrenceOrder,
    kind: OccurrenceKind,
}

impl Occurrence {
    fn sort_key(&self) -> (FinalOccurrenceOrder, u8, u64, usize, u32, usize) {
        match self.kind {
            OccurrenceKind::Read(site) => (
                self.order,
                0,
                self.block,
                self.region.index(),
                site.inst.0,
                site.input_idx,
            ),
            OccurrenceKind::Write(inst) => {
                (self.order, 1, self.block, self.region.index(), inst.0, 0)
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OccurrenceKind {
    Read(UseSite),
    Write(InstId),
}

fn lowest_dominating_region<C: PlacementControlFlow + ?Sized>(
    regions: &SealedStructuredRegionArtifact,
    cfg: &C,
    occurrences: &[Occurrence],
) -> Option<RegionId> {
    let mut candidate = occurrences.first()?.region;
    for occurrence in &occurrences[1..] {
        candidate = lowest_common_ancestor(regions, candidate, occurrence.region)?;
    }

    loop {
        let node = regions.node(candidate)?;
        if occurrences
            .iter()
            .all(|occurrence| cfg.dominates(node.entry(), occurrence.block))
        {
            return Some(candidate);
        }
        candidate = node.parent()?;
    }
}

fn lowest_common_ancestor(
    regions: &SealedStructuredRegionArtifact,
    mut left: RegionId,
    mut right: RegionId,
) -> Option<RegionId> {
    let mut left_depth = regions.node(left)?.depth();
    let mut right_depth = regions.node(right)?.depth();
    while left_depth > right_depth {
        left = regions.node(left)?.parent()?;
        left_depth -= 1;
    }
    while right_depth > left_depth {
        right = regions.node(right)?.parent()?;
        right_depth -= 1;
    }
    while left != right {
        left = regions.node(left)?.parent()?;
        right = regions.node(right)?.parent()?;
    }
    Some(left)
}

fn first_read_before_assignment(
    binding: BindingId,
    occurrences: &[Occurrence],
    must_in: &[DenseBindingSet],
    block_indices: &BTreeMap<u64, usize>,
) -> Option<UseSite> {
    let mut by_rendered_block = BTreeMap::<(u64, RegionId), Vec<&Occurrence>>::new();
    for occurrence in occurrences {
        by_rendered_block
            .entry((occurrence.block, occurrence.region))
            .or_default()
            .push(occurrence);
    }

    for ((block, _region), mut block_occurrences) in by_rendered_block {
        block_occurrences.sort_by_key(|occurrence| occurrence.sort_key());
        let block_index = block_indices[&block];
        let mut assigned = must_in[block_index].contains(binding);
        for occurrence in block_occurrences {
            match occurrence.kind {
                OccurrenceKind::Read(site) if !assigned => return Some(site),
                OccurrenceKind::Read(_) => {}
                OccurrenceKind::Write(_) => assigned = true,
            }
        }
    }
    None
}

fn must_assignment_inputs<C: PlacementControlFlow + ?Sized>(
    cfg: &C,
    binding_count: usize,
    block_addrs: &[u64],
    block_indices: &BTreeMap<u64, usize>,
    occurrences: &[Vec<Occurrence>],
) -> Vec<DenseBindingSet> {
    let mut generated = vec![DenseBindingSet::empty(binding_count); block_addrs.len()];
    for (binding_index, binding_occurrences) in occurrences.iter().enumerate() {
        let binding = BindingId::from_dense_index(binding_index)
            .expect("binding occurrence index fits BindingId");
        for occurrence in binding_occurrences {
            if matches!(occurrence.kind, OccurrenceKind::Write(_)) {
                generated[block_indices[&occurrence.block]].insert(binding);
            }
        }
    }

    let mut inputs = vec![DenseBindingSet::all(binding_count); block_addrs.len()];
    let mut outputs = vec![DenseBindingSet::all(binding_count); block_addrs.len()];
    let mut worklist = (0..block_addrs.len()).collect::<BTreeSet<_>>();
    while let Some(block_index) = worklist.pop_first() {
        let block = block_addrs[block_index];
        let mut predecessors = cfg.predecessors(block);
        predecessors.sort_unstable();
        predecessors.dedup();
        let next_input = if block == cfg.entry() || predecessors.is_empty() {
            DenseBindingSet::empty(binding_count)
        } else {
            let first = predecessors.remove(0);
            let mut intersection = outputs[block_indices[&first]].clone();
            for predecessor in predecessors {
                intersection.intersect_with(&outputs[block_indices[&predecessor]]);
            }
            intersection
        };
        let mut next_output = next_input.clone();
        next_output.union_with(&generated[block_index]);
        let output_changed = next_output != outputs[block_index];
        inputs[block_index] = next_input;
        outputs[block_index] = next_output;
        if output_changed {
            let mut successors = cfg.successors(block);
            successors.sort_unstable();
            successors.dedup();
            for successor in successors {
                worklist.insert(block_indices[&successor]);
            }
        }
    }
    inputs
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DenseBindingSet {
    words: Vec<u64>,
    binding_count: usize,
}

impl DenseBindingSet {
    fn empty(binding_count: usize) -> Self {
        Self {
            words: vec![0; binding_count.div_ceil(u64::BITS as usize)],
            binding_count,
        }
    }

    fn all(binding_count: usize) -> Self {
        let mut set = Self {
            words: vec![u64::MAX; binding_count.div_ceil(u64::BITS as usize)],
            binding_count,
        };
        if let Some(last) = set.words.last_mut() {
            let used = binding_count % u64::BITS as usize;
            if used != 0 {
                *last &= (1_u64 << used) - 1;
            }
        }
        set
    }

    fn contains(&self, binding: BindingId) -> bool {
        let index = binding.index();
        index < self.binding_count
            && self.words[index / u64::BITS as usize] & (1_u64 << (index % u64::BITS as usize)) != 0
    }

    fn insert(&mut self, binding: BindingId) {
        let index = binding.index();
        debug_assert!(index < self.binding_count);
        self.words[index / u64::BITS as usize] |= 1_u64 << (index % u64::BITS as usize);
    }

    fn intersect_with(&mut self, other: &Self) {
        debug_assert_eq!(self.binding_count, other.binding_count);
        for (left, right) in self.words.iter_mut().zip(&other.words) {
            *left &= *right;
        }
    }

    fn union_with(&mut self, other: &Self) {
        debug_assert_eq!(self.binding_count, other.binding_count);
        for (left, right) in self.words.iter_mut().zip(&other.words) {
            *left |= *right;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::region::Region;
    use crate::structured_region::{StructuredRegionDraft, StructuredRegionKind};

    #[derive(Debug)]
    struct TestCfg {
        entry: u64,
        successors: BTreeMap<u64, Vec<u64>>,
        predecessors: BTreeMap<u64, Vec<u64>>,
        dominators: BTreeMap<u64, BTreeSet<u64>>,
    }

    impl TestCfg {
        fn new(entry: u64, edges: &[(u64, u64)]) -> Self {
            let mut blocks = BTreeSet::from([entry]);
            let mut successors = BTreeMap::<u64, Vec<u64>>::new();
            let mut predecessors = BTreeMap::<u64, Vec<u64>>::new();
            for &(from, to) in edges {
                blocks.extend([from, to]);
                successors.entry(from).or_default().push(to);
                predecessors.entry(to).or_default().push(from);
            }
            for block in &blocks {
                successors.entry(*block).or_default().sort_unstable();
                predecessors.entry(*block).or_default().sort_unstable();
            }

            let mut dominators = blocks
                .iter()
                .map(|block| {
                    let set = if *block == entry {
                        BTreeSet::from([entry])
                    } else {
                        blocks.clone()
                    };
                    (*block, set)
                })
                .collect::<BTreeMap<_, _>>();
            loop {
                let mut changed = false;
                for block in blocks.iter().copied().filter(|block| *block != entry) {
                    let preds = &predecessors[&block];
                    let mut next = if let Some(first) = preds.first() {
                        dominators[first].clone()
                    } else {
                        BTreeSet::new()
                    };
                    for predecessor in preds.iter().skip(1) {
                        next = next
                            .intersection(&dominators[predecessor])
                            .copied()
                            .collect();
                    }
                    next.insert(block);
                    if next != dominators[&block] {
                        dominators.insert(block, next);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            Self {
                entry,
                successors,
                predecessors,
                dominators,
            }
        }
    }

    impl PlacementControlFlow for TestCfg {
        fn entry(&self) -> u64 {
            self.entry
        }

        fn block_addrs(&self) -> Vec<u64> {
            self.successors.keys().copied().collect()
        }

        fn predecessors(&self, block: u64) -> Vec<u64> {
            self.predecessors[&block].clone()
        }

        fn successors(&self, block: u64) -> Vec<u64> {
            self.successors[&block].clone()
        }

        fn dominates(&self, dominator: u64, block: u64) -> bool {
            self.dominators[&block].contains(&dominator)
        }
    }

    fn diamond_regions() -> SealedStructuredRegionArtifact {
        let region = Region::Sequence(vec![
            Region::IfThenElse {
                cond_block: 0x1000,
                then_region: Box::new(Region::Block(0x1010)),
                else_region: Some(Box::new(Region::Block(0x1020))),
                merge_block: Some(0x1030),
            },
            Region::Block(0x1030),
        ]);
        StructuredRegionDraft::from_region(0x1000, &region)
            .expect("diamond region")
            .seal()
    }

    fn region_with_entry(
        regions: &SealedStructuredRegionArtifact,
        entry: u64,
        kind: StructuredRegionKind,
    ) -> RegionId {
        let index = regions
            .nodes()
            .iter()
            .position(|node| node.entry() == entry && node.kind() == kind)
            .expect("region entry");
        regions
            .node_for_anchor(
                regions.authority(),
                regions.nodes()[index].emission_anchor(),
            )
            .expect("dense region")
            .0
    }

    fn diamond_cfg() -> TestCfg {
        TestCfg::new(
            0x1000,
            &[
                (0x1000, 0x1010),
                (0x1000, 0x1020),
                (0x1010, 0x1030),
                (0x1020, 0x1030),
            ],
        )
    }

    #[test]
    fn diamond_with_both_arms_assigned_places_one_lexical_declaration() {
        let regions = diamond_regions();
        let cfg = diamond_cfg();
        let binding = BindingId::from_dense_index(0).expect("binding");
        let then_region = region_with_entry(&regions, 0x1010, StructuredRegionKind::Block);
        let else_region = region_with_entry(&regions, 0x1020, StructuredRegionKind::Block);
        let merge_region = region_with_entry(&regions, 0x1030, StructuredRegionKind::Block);
        let writes = [
            FinalBindingWrite {
                binding,
                inst: InstId(1),
                region: then_region,
                block: 0x1010,
                order: FinalOccurrenceOrder(1),
            },
            FinalBindingWrite {
                binding,
                inst: InstId(2),
                region: else_region,
                block: 0x1020,
                order: FinalOccurrenceOrder(2),
            },
        ];
        let reads = [FinalBindingRead {
            binding,
            site: UseSite {
                inst: InstId(3),
                input_idx: 0,
            },
            region: merge_region,
            block: 0x1030,
            order: FinalOccurrenceOrder(3),
        }];

        let decisions = derive_with_cfg(&regions, &cfg, 1, &reads, &writes).expect("placement");
        let sequence = regions.source_root();
        assert_eq!(
            decisions.decision(binding),
            Some(PlacementDecision::LexicalDeclaration { region: sequence })
        );
    }

    #[test]
    fn diamond_with_one_arm_unassigned_refuses_merge_read() {
        let regions = diamond_regions();
        let cfg = diamond_cfg();
        let binding = BindingId::from_dense_index(0).expect("binding");
        let then_region = region_with_entry(&regions, 0x1010, StructuredRegionKind::Block);
        let merge_region = region_with_entry(&regions, 0x1030, StructuredRegionKind::Block);
        let site = UseSite {
            inst: InstId(3),
            input_idx: 0,
        };
        let writes = [FinalBindingWrite {
            binding,
            inst: InstId(1),
            region: then_region,
            block: 0x1010,
            order: FinalOccurrenceOrder(1),
        }];
        let reads = [FinalBindingRead {
            binding,
            site,
            region: merge_region,
            block: 0x1030,
            order: FinalOccurrenceOrder(2),
        }];

        let decisions = derive_with_cfg(&regions, &cfg, 1, &reads, &writes).expect("placement");
        assert_eq!(
            decisions.decision(binding),
            Some(PlacementDecision::Refused(
                PlacementRefusal::ReadBeforeAssignment { binding, site }
            ))
        );
    }

    #[test]
    fn one_dominating_write_is_inlined_at_its_exact_assignment() {
        let region = Region::Sequence(vec![Region::Block(0x1000), Region::Block(0x1010)]);
        let regions = StructuredRegionDraft::from_region(0x1000, &region)
            .expect("linear region")
            .seal();
        let cfg = TestCfg::new(0x1000, &[(0x1000, 0x1010)]);
        let binding = BindingId::from_dense_index(0).expect("binding");
        let write_region = region_with_entry(&regions, 0x1000, StructuredRegionKind::Block);
        let read_region = region_with_entry(&regions, 0x1010, StructuredRegionKind::Block);
        let write = InstId(1);
        let decisions = derive_with_cfg(
            &regions,
            &cfg,
            1,
            &[FinalBindingRead {
                binding,
                site: UseSite {
                    inst: InstId(2),
                    input_idx: 0,
                },
                region: read_region,
                block: 0x1010,
                order: FinalOccurrenceOrder(2),
            }],
            &[FinalBindingWrite {
                binding,
                inst: write,
                region: write_region,
                block: 0x1000,
                order: FinalOccurrenceOrder(1),
            }],
        )
        .expect("placement");

        assert_eq!(
            decisions.decision(binding),
            Some(PlacementDecision::Inline { write })
        );
    }
}
