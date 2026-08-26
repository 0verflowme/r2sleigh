//! Whole-function structural validation for canonical SSA.
//!
//! This validator checks facts that cannot be established by looking at one
//! operation in isolation: every non-entry value has exactly one definition,
//! phi inputs stay aligned with CFG predecessors, and phi storage/width facts
//! agree with the exact SSA value they describe.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::function::{DefSite, SSAFunction, SourceSite};
use crate::{CanonicalStorageId, SSAOp, SSAVar};

/// The scalar-width rule violated by one regular SSA operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarWidthRule {
    /// A copy preserves the exact bitvector width.
    CopyPreservesWidth,
    /// Integer comparisons produce a one-byte boolean value.
    ComparisonProducesBoolean,
    /// Both integer-comparison operands have the same width.
    ComparisonOperandsMatch,
    /// An extension strictly increases the source width.
    ExtensionWidens,
}

/// A whole-function SSA invariant violation.
#[derive(Debug, Clone, PartialEq)]
pub enum SsaIntegrityError {
    BlockOrderMismatch {
        ordered: Vec<u64>,
        stored_count: usize,
    },
    EntryOutsideBlockDomain {
        entry: u64,
    },
    PredecessorOutsideBlockDomain {
        block_addr: u64,
        predecessor: u64,
    },
    SuccessorOutsideBlockDomain {
        block_addr: u64,
        successor: u64,
    },
    PredecessorNotReciprocal {
        block_addr: u64,
        predecessor: u64,
    },
    SuccessorNotReciprocal {
        block_addr: u64,
        successor: u64,
    },
    DefinitionAtVersionZero {
        block_addr: u64,
        site: DefSite,
        var: SSAVar,
    },
    DuplicateDefinition {
        var: SSAVar,
        first_block_addr: u64,
        first_site: DefSite,
        duplicate_block_addr: u64,
        duplicate_site: DefSite,
    },
    MissingDefinition {
        block_addr: u64,
        site: SourceSite,
        var: SSAVar,
    },
    PhiPredecessorMismatch {
        block_addr: u64,
        phi_idx: usize,
        expected: Vec<u64>,
        actual: Vec<u64>,
    },
    PhiWidthMismatch {
        block_addr: u64,
        phi_idx: usize,
        dst: SSAVar,
        source_idx: usize,
        source: SSAVar,
    },
    PhiStorageMismatch {
        block_addr: u64,
        phi_idx: usize,
        dst: SSAVar,
        declared: CanonicalStorageId,
        retained: Option<CanonicalStorageId>,
    },
    ScalarWidthMismatch {
        block_addr: u64,
        op_idx: usize,
        rule: ScalarWidthRule,
        op: SSAOp,
    },
    ZeroWidthValue {
        block_addr: u64,
        site: SsaValueSite,
        var: SSAVar,
    },
}

/// Exact site at which a zero-width SSA value was observed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SsaValueSite {
    Definition(DefSite),
    Source(SourceSite),
}

impl fmt::Display for SsaIntegrityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BlockOrderMismatch {
                ordered,
                stored_count,
            } => write!(
                f,
                "SSA block order {ordered:?} does not bijectively cover {stored_count} stored blocks"
            ),
            Self::EntryOutsideBlockDomain { entry } => write!(
                f,
                "SSA entry 0x{entry:x} is not present in the stored block domain"
            ),
            Self::PredecessorOutsideBlockDomain {
                block_addr,
                predecessor,
            } => write!(
                f,
                "SSA block 0x{block_addr:x} has CFG predecessor 0x{predecessor:x} outside the stored block domain"
            ),
            Self::SuccessorOutsideBlockDomain {
                block_addr,
                successor,
            } => write!(
                f,
                "SSA block 0x{block_addr:x} has CFG successor 0x{successor:x} outside the stored block domain"
            ),
            Self::PredecessorNotReciprocal {
                block_addr,
                predecessor,
            } => write!(
                f,
                "SSA block 0x{block_addr:x} names CFG predecessor 0x{predecessor:x}, but that predecessor does not name the block as a successor"
            ),
            Self::SuccessorNotReciprocal {
                block_addr,
                successor,
            } => write!(
                f,
                "SSA block 0x{block_addr:x} names CFG successor 0x{successor:x}, but that successor does not name the block as a predecessor"
            ),
            Self::DefinitionAtVersionZero {
                block_addr,
                site,
                var,
            } => write!(
                f,
                "SSA destination {var} at {site:?} in block 0x{block_addr:x} has version zero"
            ),
            Self::DuplicateDefinition {
                var,
                first_block_addr,
                first_site,
                duplicate_block_addr,
                duplicate_site,
            } => write!(
                f,
                "SSA value {var} is defined twice: {first_site:?} in block \
                 0x{first_block_addr:x} and {duplicate_site:?} in block \
                 0x{duplicate_block_addr:x}"
            ),
            Self::MissingDefinition {
                block_addr,
                site,
                var,
            } => write!(
                f,
                "non-entry SSA use {var} at {site:?} in block 0x{block_addr:x} has no exact definition"
            ),
            Self::PhiPredecessorMismatch {
                block_addr,
                phi_idx,
                expected,
                actual,
            } => write!(
                f,
                "phi {phi_idx} in block 0x{block_addr:x} has predecessor sequence \
                 {actual:?}, expected {expected:?}"
            ),
            Self::PhiWidthMismatch {
                block_addr,
                phi_idx,
                dst,
                source_idx,
                source,
            } => write!(
                f,
                "phi {phi_idx} source {source_idx} ({source}) in block 0x{block_addr:x} \
                 does not match destination {dst} width"
            ),
            Self::PhiStorageMismatch {
                block_addr,
                phi_idx,
                dst,
                declared,
                retained,
            } => write!(
                f,
                "phi {phi_idx} in block 0x{block_addr:x} declares storage {declared:?} \
                 for {dst}, but its retained storage is {retained:?}"
            ),
            Self::ScalarWidthMismatch {
                block_addr,
                op_idx,
                rule,
                ..
            } => write!(
                f,
                "SSA operation {op_idx} in block 0x{block_addr:x} violates scalar-width rule {rule:?}"
            ),
            Self::ZeroWidthValue {
                block_addr,
                site,
                var,
            } => write!(
                f,
                "SSA value {var} at {site:?} in block 0x{block_addr:x} has zero width"
            ),
        }
    }
}

impl std::error::Error for SsaIntegrityError {}

#[derive(Debug, Clone, Copy)]
struct DefinitionLocation {
    block_addr: u64,
    site: DefSite,
}

#[derive(Debug)]
struct BlockTopology {
    predecessors: Vec<u64>,
    successors: Vec<u64>,
    predecessor_set: HashSet<u64>,
    successor_set: HashSet<u64>,
}

/// Validate the structural and scalar-width invariants of one SSA function.
///
/// Version zero is the explicit entry/live-in domain, so version-zero sources
/// (including constants) need no definition. Every source with a nonzero
/// version must match one exact [`SSAVar`] definition. The scan is
/// deterministic and linear in definitions, uses, and CFG edges (with
/// expected constant-time hash lookups).
pub fn validate_ssa_function(function: &SSAFunction) -> Result<(), SsaIntegrityError> {
    let ordered = function.block_addrs();
    let block_domain = ordered.iter().copied().collect::<HashSet<_>>();
    if ordered.len() != function.num_blocks()
        || block_domain.len() != ordered.len()
        || ordered
            .iter()
            .any(|addr| function.get_block(*addr).is_none())
    {
        return Err(SsaIntegrityError::BlockOrderMismatch {
            ordered: ordered.to_vec(),
            stored_count: function.num_blocks(),
        });
    }
    if !block_domain.contains(&function.entry) {
        return Err(SsaIntegrityError::EntryOutsideBlockDomain {
            entry: function.entry,
        });
    }

    // `SsaGraph` stores only `block_order`, so every retained CFG edge must be
    // closed over that exact domain. Cache both directions once: deterministic
    // iteration follows `block_order` and the CFG's stable adjacency order,
    // while reciprocal membership remains expected O(1) per edge.
    let topology = ordered
        .iter()
        .map(|addr| {
            let predecessors = function.predecessors(*addr);
            let successors = function.successors(*addr);
            (
                *addr,
                BlockTopology {
                    predecessor_set: predecessors.iter().copied().collect(),
                    successor_set: successors.iter().copied().collect(),
                    predecessors,
                    successors,
                },
            )
        })
        .collect::<HashMap<_, _>>();

    for block_addr in ordered {
        let block_topology = topology
            .get(block_addr)
            .expect("topology is indexed from the validated block order");
        for predecessor in &block_topology.predecessors {
            if !block_domain.contains(predecessor) {
                return Err(SsaIntegrityError::PredecessorOutsideBlockDomain {
                    block_addr: *block_addr,
                    predecessor: *predecessor,
                });
            }
            let predecessor_topology = topology
                .get(predecessor)
                .expect("stored-domain predecessor has cached topology");
            if !predecessor_topology.successor_set.contains(block_addr) {
                return Err(SsaIntegrityError::PredecessorNotReciprocal {
                    block_addr: *block_addr,
                    predecessor: *predecessor,
                });
            }
        }
        for successor in &block_topology.successors {
            if !block_domain.contains(successor) {
                return Err(SsaIntegrityError::SuccessorOutsideBlockDomain {
                    block_addr: *block_addr,
                    successor: *successor,
                });
            }
            let successor_topology = topology
                .get(successor)
                .expect("stored-domain successor has cached topology");
            if !successor_topology.predecessor_set.contains(block_addr) {
                return Err(SsaIntegrityError::SuccessorNotReciprocal {
                    block_addr: *block_addr,
                    successor: *successor,
                });
            }
        }
    }

    let mut definitions = HashMap::<SSAVar, DefinitionLocation>::new();

    // Complete the definition table before checking uses: a legal SSA use can
    // precede its textual definition through a loop-carried phi edge.
    for block in function.blocks() {
        let mut failure = None;
        block.for_each_def(|definition| {
            if failure.is_some() {
                return;
            }
            let var = definition.var;
            if var.size == 0 {
                failure = Some(SsaIntegrityError::ZeroWidthValue {
                    block_addr: block.addr,
                    site: SsaValueSite::Definition(definition.site),
                    var: var.clone(),
                });
                return;
            }
            if var.version == 0 {
                failure = Some(SsaIntegrityError::DefinitionAtVersionZero {
                    block_addr: block.addr,
                    site: definition.site,
                    var: var.clone(),
                });
                return;
            }
            let location = DefinitionLocation {
                block_addr: block.addr,
                site: definition.site,
            };
            if let Some(first) = definitions.insert(var.clone(), location) {
                failure = Some(SsaIntegrityError::DuplicateDefinition {
                    var: var.clone(),
                    first_block_addr: first.block_addr,
                    first_site: first.site,
                    duplicate_block_addr: block.addr,
                    duplicate_site: definition.site,
                });
            }
        });
        if let Some(failure) = failure {
            return Err(failure);
        }
    }

    for block in function.blocks() {
        // Query once per block so the full validator remains linear in CFG
        // edges even when a merge block carries several phi values.
        let expected_predecessors = topology
            .get(&block.addr)
            .expect("validated SSA block has cached topology")
            .predecessors
            .clone();

        for (phi_idx, phi) in block.phis.iter().enumerate() {
            let actual_predecessors = phi
                .sources
                .iter()
                .map(|(predecessor, _)| *predecessor)
                .collect::<Vec<_>>();
            let mut seen_predecessors = HashSet::with_capacity(actual_predecessors.len());
            let has_duplicate = actual_predecessors
                .iter()
                .any(|predecessor| !seen_predecessors.insert(*predecessor));
            if has_duplicate || actual_predecessors != expected_predecessors {
                return Err(SsaIntegrityError::PhiPredecessorMismatch {
                    block_addr: block.addr,
                    phi_idx,
                    expected: expected_predecessors,
                    actual: actual_predecessors,
                });
            }

            for (source_idx, (pred_addr, source)) in phi.sources.iter().enumerate() {
                if source.size == 0 {
                    return Err(SsaIntegrityError::ZeroWidthValue {
                        block_addr: block.addr,
                        site: SsaValueSite::Source(SourceSite::Phi {
                            phi_idx,
                            src_idx: source_idx,
                            pred_addr: *pred_addr,
                        }),
                        var: source.clone(),
                    });
                }
                if source.size != phi.dst.size {
                    return Err(SsaIntegrityError::PhiWidthMismatch {
                        block_addr: block.addr,
                        phi_idx,
                        dst: phi.dst.clone(),
                        source_idx,
                        source: source.clone(),
                    });
                }
            }

            if let Some(declared) = phi.canonical_storage {
                let retained = function.canonical_storage_for_var(&phi.dst);
                if declared.size != phi.dst.size || retained != Some(declared) {
                    return Err(SsaIntegrityError::PhiStorageMismatch {
                        block_addr: block.addr,
                        phi_idx,
                        dst: phi.dst.clone(),
                        declared,
                        retained,
                    });
                }
            }
        }

        for (op_idx, op) in block.ops.iter().enumerate() {
            let mut zero_width_source = None;
            let mut source_idx = 0usize;
            op.for_each_source(|source| {
                if zero_width_source.is_none() && source.size == 0 {
                    zero_width_source = Some((source_idx, source.clone()));
                }
                source_idx += 1;
            });
            if let Some((src_idx, var)) = zero_width_source {
                return Err(SsaIntegrityError::ZeroWidthValue {
                    block_addr: block.addr,
                    site: SsaValueSite::Source(SourceSite::Op { op_idx, src_idx }),
                    var,
                });
            }
            if let Some(rule) = scalar_width_violation(op) {
                return Err(SsaIntegrityError::ScalarWidthMismatch {
                    block_addr: block.addr,
                    op_idx,
                    rule,
                    op: op.clone(),
                });
            }
        }

        let mut failure = None;
        block.for_each_source(|source| {
            if failure.is_some() {
                return;
            }
            if source.var.size == 0 {
                failure = Some(SsaIntegrityError::ZeroWidthValue {
                    block_addr: block.addr,
                    site: SsaValueSite::Source(source.site),
                    var: source.var.clone(),
                });
                return;
            }
            if source.var.version != 0 && !definitions.contains_key(source.var) {
                failure = Some(SsaIntegrityError::MissingDefinition {
                    block_addr: block.addr,
                    site: source.site,
                    var: source.var.clone(),
                });
            }
        });
        if let Some(failure) = failure {
            return Err(failure);
        }
    }

    Ok(())
}

fn scalar_width_violation(op: &SSAOp) -> Option<ScalarWidthRule> {
    match op {
        SSAOp::Copy { dst, src } if dst.size != src.size => {
            Some(ScalarWidthRule::CopyPreservesWidth)
        }
        SSAOp::IntEqual { dst, .. }
        | SSAOp::IntNotEqual { dst, .. }
        | SSAOp::IntLess { dst, .. }
        | SSAOp::IntSLess { dst, .. }
        | SSAOp::IntLessEqual { dst, .. }
        | SSAOp::IntSLessEqual { dst, .. }
            if dst.size != 1 =>
        {
            Some(ScalarWidthRule::ComparisonProducesBoolean)
        }
        SSAOp::IntEqual { a, b, .. }
        | SSAOp::IntNotEqual { a, b, .. }
        | SSAOp::IntLess { a, b, .. }
        | SSAOp::IntSLess { a, b, .. }
        | SSAOp::IntLessEqual { a, b, .. }
        | SSAOp::IntSLessEqual { a, b, .. }
            if a.size != b.size =>
        {
            Some(ScalarWidthRule::ComparisonOperandsMatch)
        }
        SSAOp::IntZExt { dst, src } | SSAOp::IntSExt { dst, src } if dst.size <= src.size => {
            Some(ScalarWidthRule::ExtensionWidens)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PhiNode;
    use crate::cfg::{BasicBlock, BlockTerminator};
    use r2il::{R2ILBlock, R2ILOp, SpaceId, Varnode};

    fn constant(value: u64, size: u32) -> Varnode {
        Varnode::new(SpaceId::Const, value, size)
    }

    fn register(offset: u64, size: u32) -> Varnode {
        Varnode::new(SpaceId::Register, offset, size)
    }

    fn diamond() -> SSAFunction {
        let blocks = [
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: constant(0x1008, 8),
                    cond: constant(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: register(0, 8),
                        src: constant(1, 8),
                    },
                    R2ILOp::Branch {
                        target: constant(0x100c, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: register(0, 8),
                        src: constant(2, 8),
                    },
                    R2ILOp::Branch {
                        target: constant(0x100c, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                ops: vec![R2ILOp::IntAdd {
                    dst: register(8, 8),
                    a: register(0, 8),
                    b: constant(3, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        SSAFunction::from_blocks_raw_no_arch(&blocks).expect("diamond must form SSA")
    }

    #[test]
    fn accepts_a_well_formed_function() {
        validate_ssa_function(&diamond()).expect("constructed SSA must be internally coherent");
    }

    #[test]
    fn rejects_entry_outside_the_stored_block_domain() {
        let mut function = diamond();
        function.remove_block(function.entry);

        assert_eq!(
            validate_ssa_function(&function),
            Err(SsaIntegrityError::EntryOutsideBlockDomain { entry: 0x1000 })
        );
    }

    #[test]
    fn rejects_cfg_edges_that_leave_the_stored_block_domain() {
        let mut predecessor = diamond();
        let mut orphan = BasicBlock::new(0x3000);
        orphan.terminator = BlockTerminator::Branch { target: 0x100c };
        predecessor.cfg_mut().add_block(orphan);
        predecessor.cfg_mut().rebuild_edges();
        assert_eq!(
            validate_ssa_function(&predecessor),
            Err(SsaIntegrityError::PredecessorOutsideBlockDomain {
                block_addr: 0x100c,
                predecessor: 0x3000,
            })
        );

        let mut successor = diamond();
        let mut orphan = BasicBlock::new(0x3000);
        orphan.terminator = BlockTerminator::Return;
        successor.cfg_mut().add_block(orphan);
        successor
            .cfg_mut()
            .set_terminator(0x1004, BlockTerminator::Branch { target: 0x3000 });
        assert_eq!(
            validate_ssa_function(&successor),
            Err(SsaIntegrityError::SuccessorOutsideBlockDomain {
                block_addr: 0x1004,
                successor: 0x3000,
            })
        );
    }

    #[test]
    fn rejects_nonreciprocal_cfg_topology_before_graph_construction() {
        let mut function = diamond();
        // A duplicate CFG address makes the address index name the new node,
        // while existing edges still target the old node. The public topology
        // queries then disagree even though every reported address is stored.
        function.cfg_mut().add_block(BasicBlock::new(0x1008));

        assert_eq!(
            validate_ssa_function(&function),
            Err(SsaIntegrityError::SuccessorNotReciprocal {
                block_addr: 0x1000,
                successor: 0x1008,
            })
        );
    }

    #[test]
    fn symbolic_constructor_refuses_runtime_alias_overlap_with_disconnected_predecessor() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: register(0, 8),
                        src: constant(0x11, 8),
                    },
                    R2ILOp::Branch {
                        target: constant(0x1020, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x3000,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: register(0, 8),
                        src: constant(0x22, 8),
                    },
                    R2ILOp::Branch {
                        target: constant(0x1020, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1020,
                size: 1,
                ops: vec![R2ILOp::Nop],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        assert!(crate::SsaArtifact::for_symbolic(&blocks, None).is_none());
    }

    #[test]
    fn symbolic_constructor_refuses_large_fanout_with_disconnected_tail() {
        let mut blocks = Vec::new();
        for idx in 0..50u64 {
            blocks.push(R2ILBlock {
                addr: 0x3000 + idx * 8,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: constant(0x3100, 8),
                    cond: register(0, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            });
            blocks.push(R2ILBlock {
                addr: 0x3004 + idx * 8,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: constant(0x3008 + idx * 8, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            });
        }
        blocks.push(R2ILBlock {
            addr: 0x3100,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: register(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        });

        assert!(crate::SsaArtifact::for_symbolic(&blocks, None).is_none());
    }

    #[test]
    fn rejects_a_nonzero_use_without_an_exact_definition() {
        let mut function = diamond();
        let merge = function.get_block_mut(0x100c).expect("merge block");
        let SSAOp::IntAdd { a, .. } = &mut merge.ops[0] else {
            panic!("expected merge use");
        };
        *a = SSAVar::new("reg:dead", 7, 8);

        assert!(matches!(
            validate_ssa_function(&function),
            Err(SsaIntegrityError::MissingDefinition {
                block_addr: 0x100c,
                site: SourceSite::Op {
                    op_idx: 0,
                    src_idx: 0
                },
                ..
            })
        ));
    }

    #[test]
    fn rejects_duplicate_and_version_zero_definitions() {
        let mut duplicate = diamond();
        let block = duplicate.get_block_mut(0x1004).expect("left block");
        let dst = block.ops[0].dst().expect("copy destination").clone();
        block.ops.push(SSAOp::Copy {
            dst,
            src: SSAVar::constant(9, 8),
        });
        assert!(matches!(
            validate_ssa_function(&duplicate),
            Err(SsaIntegrityError::DuplicateDefinition { .. })
        ));

        let mut zero = diamond();
        let block = zero.get_block_mut(0x1004).expect("left block");
        let dst = block.ops[0].dst().expect("copy destination").clone();
        let SSAOp::Copy { dst: written, .. } = &mut block.ops[0] else {
            unreachable!();
        };
        *written = SSAVar::new(dst.name, 0, dst.size);
        assert!(matches!(
            validate_ssa_function(&zero),
            Err(SsaIntegrityError::DefinitionAtVersionZero { .. })
        ));
    }

    #[test]
    fn rejects_phi_predecessor_width_and_storage_drift() {
        let mut predecessor = diamond();
        predecessor.get_block_mut(0x100c).expect("merge block").phis[0]
            .sources
            .pop();
        assert!(matches!(
            validate_ssa_function(&predecessor),
            Err(SsaIntegrityError::PhiPredecessorMismatch { .. })
        ));

        let mut width = diamond();
        let phi = &mut width.get_block_mut(0x100c).expect("merge block").phis[0];
        let old = phi.sources[0].1.clone();
        phi.sources[0].1 = SSAVar::new(old.name, old.version, 4);
        assert!(matches!(
            validate_ssa_function(&width),
            Err(SsaIntegrityError::PhiWidthMismatch { .. })
        ));

        let mut storage = diamond();
        let phi = &mut storage.get_block_mut(0x100c).expect("merge block").phis[0];
        let mut declared = phi.canonical_storage.expect("lifted phi storage");
        declared.offset += 1;
        phi.canonical_storage = Some(declared);
        assert!(matches!(
            validate_ssa_function(&storage),
            Err(SsaIntegrityError::PhiStorageMismatch { .. })
        ));
    }

    #[test]
    fn rejects_scalar_width_drift_and_zero_width_values() {
        let mut scalar = diamond();
        let merge = scalar.get_block_mut(0x100c).expect("merge block");
        let dst = merge.ops[0].dst().expect("merge destination").clone();
        merge.ops[0] = SSAOp::Copy {
            dst,
            src: SSAVar::constant(3, 4),
        };
        assert!(matches!(
            validate_ssa_function(&scalar),
            Err(SsaIntegrityError::ScalarWidthMismatch {
                rule: ScalarWidthRule::CopyPreservesWidth,
                ..
            })
        ));

        let mut zero = diamond();
        let merge = zero.get_block_mut(0x100c).expect("merge block");
        let SSAOp::IntAdd { b, .. } = &mut merge.ops[0] else {
            unreachable!();
        };
        *b = SSAVar::constant(3, 0);
        assert!(matches!(
            validate_ssa_function(&zero),
            Err(SsaIntegrityError::ZeroWidthValue {
                site: SsaValueSite::Source(SourceSite::Op {
                    op_idx: 0,
                    src_idx: 1
                }),
                ..
            })
        ));
    }

    #[test]
    fn accepts_constant_and_cross_name_phi_sources_with_exact_provenance() {
        let mut function = diamond();
        let source = function.get_block(0x1004).expect("left block").ops[0]
            .dst()
            .expect("left definition")
            .clone();
        let alias = SSAVar::new("tmp:regalias:phi", source.version, source.size);
        function.get_block_mut(0x1004).expect("left block").ops[0] = SSAOp::Subpiece {
            dst: alias.clone(),
            src: SSAVar::initial("tmp:regalias:wide", 16),
            offset: 0,
        };

        let phi = &mut function.get_block_mut(0x100c).expect("merge block").phis[0];
        let left_source = phi
            .sources
            .iter_mut()
            .find(|(predecessor, _)| *predecessor == 0x1004)
            .expect("left phi source");
        left_source.1 = alias;
        let right_source = phi
            .sources
            .iter_mut()
            .find(|(predecessor, _)| *predecessor == 0x1008)
            .expect("right phi source");
        right_source.1 = SSAVar::constant(2, phi.dst.size);

        validate_ssa_function(&function)
            .expect("phi inputs need exact definitions and widths, not matching names");
    }

    #[test]
    fn predecessor_order_is_part_of_the_phi_contract() {
        let mut function = diamond();
        function.get_block_mut(0x100c).expect("merge block").phis[0]
            .sources
            .swap(0, 1);

        assert!(matches!(
            validate_ssa_function(&function),
            Err(SsaIntegrityError::PhiPredecessorMismatch { .. })
        ));
    }

    #[test]
    fn public_phi_shape_remains_accepted_without_storage_provenance() {
        let mut function = diamond();
        let phi = &mut function.get_block_mut(0x100c).expect("merge block").phis[0];
        *phi = PhiNode {
            dst: phi.dst.clone(),
            sources: phi.sources.clone(),
            canonical_storage: None,
        };

        validate_ssa_function(&function).expect("absent provenance is not fabricated");
    }
}
