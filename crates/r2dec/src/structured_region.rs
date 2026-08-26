//! Immutable lexical-region identity for the final lowering phases.
//!
//! [`Region`](crate::region::Region) is an analysis result.  The control-flow
//! structurer currently consumes that result while it builds the C AST, and it
//! can append shared joins and shared exits that were not children of the raw
//! region tree.  Declaration placement therefore cannot use either block
//! addresses (one block may have several rendered occurrences) or the discarded
//! analysis tree.
//!
//! This module owns the occurrence identity that the structurer will retain.
//! A draft records the raw region tree in render order and any later synthetic
//! root appends.  Sealing consumes the draft, leaving one immutable dense tree.
//! It deliberately contains no declaration-placement answer: placement is a
//! pure calculation over this artifact and the surviving binding occurrences.

#![allow(
    dead_code,
    reason = "Stage 7 region identity lands before its structurer and placement cutovers"
)]

use std::sync::Arc;

use crate::region::Region;

/// Dense identity of one lexical region occurrence in a sealed artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RegionId(u32);

impl RegionId {
    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Dense identity carried by the C statement emitted for one region occurrence.
///
/// This is intentionally distinct from a block address.  Structuring may emit
/// one CFG block more than once, while every emitted occurrence has exactly one
/// anchor.  The artifact authority must accompany an anchor at a consumer seam;
/// the small integer alone is only meaningful inside its issuing artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RegionEmissionAnchor(u32);

impl RegionEmissionAnchor {
    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Run-local identity of one sealed structured-region artifact.
#[derive(Clone)]
pub(crate) struct StructuredRegionArtifactAuthority(Arc<()>);

impl StructuredRegionArtifactAuthority {
    fn new() -> Self {
        Self(Arc::new(()))
    }
}

impl std::fmt::Debug for StructuredRegionArtifactAuthority {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("StructuredRegionArtifactAuthority(..)")
    }
}

impl PartialEq for StructuredRegionArtifactAuthority {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for StructuredRegionArtifactAuthority {}

impl std::hash::Hash for StructuredRegionArtifactAuthority {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&Arc::as_ptr(&self.0), state);
    }
}

/// Shape of one retained lexical occurrence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StructuredRegionKind {
    FunctionBody,
    Block,
    Sequence,
    IfThenElse,
    WhileLoop,
    DoWhileLoop,
    MultiExit,
    Transfer,
    Switch,
    Irreducible,
    Synthetic(SyntheticRegionKind),
}

/// Why a statement occurrence exists outside the analyzed [`Region`] tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SyntheticRegionKind {
    SharedJoin,
    DeferredSharedExit,
}

/// One immutable lexical occurrence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StructuredRegionNode {
    parent: Option<RegionId>,
    depth: u32,
    entry: u64,
    children: Box<[RegionId]>,
    emission_anchor: RegionEmissionAnchor,
    kind: StructuredRegionKind,
}

impl StructuredRegionNode {
    pub(crate) const fn parent(&self) -> Option<RegionId> {
        self.parent
    }

    pub(crate) const fn depth(&self) -> u32 {
        self.depth
    }

    pub(crate) const fn entry(&self) -> u64 {
        self.entry
    }

    pub(crate) fn children(&self) -> &[RegionId] {
        &self.children
    }

    pub(crate) const fn emission_anchor(&self) -> RegionEmissionAnchor {
        self.emission_anchor
    }

    pub(crate) const fn kind(&self) -> StructuredRegionKind {
        self.kind
    }
}

/// Immutable lexical-region artifact consumed by placement and final emission.
#[derive(Debug, Clone)]
pub(crate) struct SealedStructuredRegionArtifact {
    authority: StructuredRegionArtifactAuthority,
    root: RegionId,
    nodes: Box<[StructuredRegionNode]>,
}

impl SealedStructuredRegionArtifact {
    pub(crate) const fn authority(&self) -> &StructuredRegionArtifactAuthority {
        &self.authority
    }

    pub(crate) const fn root(&self) -> RegionId {
        self.root
    }

    /// Root of the analyzed tree below the explicit function-body scope.
    pub(crate) fn source_root(&self) -> RegionId {
        self.nodes[self.root.index()].children[0]
    }

    /// Children already retained for `id`, in exact render order.
    pub(crate) fn children(&self, id: RegionId) -> Option<&[RegionId]> {
        self.nodes
            .get(id.index())
            .map(|node| node.children.as_ref())
    }

    /// Anchor that the structurer must attach to the emitted occurrence.
    pub(crate) fn emission_anchor(&self, id: RegionId) -> Option<RegionEmissionAnchor> {
        self.nodes.get(id.index()).map(|node| node.emission_anchor)
    }

    pub(crate) fn nodes(&self) -> &[StructuredRegionNode] {
        &self.nodes
    }

    pub(crate) fn node(&self, id: RegionId) -> Option<&StructuredRegionNode> {
        self.nodes.get(id.index())
    }

    /// Resolve an emitted occurrence without scanning the region tree.
    ///
    /// Anchors and nodes are minted in the same dense order.  Keeping this
    /// lookup structural avoids a second map whose contents could drift.
    pub(crate) fn node_for_anchor(
        &self,
        authority: &StructuredRegionArtifactAuthority,
        anchor: RegionEmissionAnchor,
    ) -> Option<(RegionId, &StructuredRegionNode)> {
        if authority != &self.authority {
            return None;
        }
        let node = self.nodes.get(anchor.index())?;
        Some((RegionId(anchor.0), node))
    }
}

/// Failure to retain a region tree without truncating a dense identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StructuredRegionBuildError {
    TooManyRegions,
    RegionDepthOverflow,
}

#[derive(Debug)]
struct DraftNode {
    parent: Option<RegionId>,
    depth: u32,
    entry: u64,
    children: Vec<RegionId>,
    emission_anchor: RegionEmissionAnchor,
    kind: StructuredRegionKind,
}

/// Mutable construction state owned only by the structuring pass.
///
/// The function-body root is explicit because shared joins and deferred shared
/// exits are lexical siblings *after* the analyzed root, not children of an
/// arbitrary final raw region.  Synthetic appends are recorded in the same
/// order in which their statements are emitted.
pub(crate) struct StructuredRegionDraft {
    authority: StructuredRegionArtifactAuthority,
    root: RegionId,
    nodes: Vec<DraftNode>,
}

impl StructuredRegionDraft {
    /// Retain one analyzed region tree in deterministic render preorder.
    pub(crate) fn from_region(
        function_entry: u64,
        region: &Region,
    ) -> Result<Self, StructuredRegionBuildError> {
        let mut draft = Self {
            authority: StructuredRegionArtifactAuthority::new(),
            root: RegionId(0),
            nodes: Vec::new(),
        };
        let root = draft.push_node(None, 0, function_entry, StructuredRegionKind::FunctionBody)?;
        debug_assert_eq!(root, draft.root);

        // An explicit stack avoids adding another recursion limit beside the
        // structurer's existing work budget.  Children are pushed in reverse so
        // allocation remains the exact forward render preorder.
        let mut pending = vec![(root, region)];
        while let Some((parent, current)) = pending.pop() {
            let depth = draft.nodes[parent.index()]
                .depth
                .checked_add(1)
                .ok_or(StructuredRegionBuildError::RegionDepthOverflow)?;
            let id = draft.push_node(Some(parent), depth, current.entry(), kind_of(current))?;
            draft.nodes[parent.index()].children.push(id);

            let children = direct_children(current);
            for child in children.into_iter().rev() {
                pending.push((id, child));
            }
        }
        Ok(draft)
    }

    pub(crate) const fn authority(&self) -> &StructuredRegionArtifactAuthority {
        &self.authority
    }

    pub(crate) const fn root(&self) -> RegionId {
        self.root
    }

    /// Root of the analyzed tree below the explicit function-body scope.
    pub(crate) fn source_root(&self) -> RegionId {
        self.nodes[self.root.index()].children[0]
    }

    /// Children already retained for `id`, in exact render order.
    pub(crate) fn children(&self, id: RegionId) -> Option<&[RegionId]> {
        self.nodes
            .get(id.index())
            .map(|node| node.children.as_slice())
    }

    /// Anchor that the structurer must attach to the emitted occurrence.
    pub(crate) fn emission_anchor(&self, id: RegionId) -> Option<RegionEmissionAnchor> {
        self.nodes.get(id.index()).map(|node| node.emission_anchor)
    }

    /// Record one root-level statement appended after the analyzed region.
    pub(crate) fn append_synthetic(
        &mut self,
        kind: SyntheticRegionKind,
        entry: u64,
    ) -> Result<(RegionId, RegionEmissionAnchor), StructuredRegionBuildError> {
        let depth = self.nodes[self.root.index()]
            .depth
            .checked_add(1)
            .ok_or(StructuredRegionBuildError::RegionDepthOverflow)?;
        let id = self.push_node(
            Some(self.root),
            depth,
            entry,
            StructuredRegionKind::Synthetic(kind),
        )?;
        self.nodes[self.root.index()].children.push(id);
        Ok((id, self.nodes[id.index()].emission_anchor))
    }

    /// Consume all mutable construction state and expose an immutable artifact.
    pub(crate) fn seal(self) -> SealedStructuredRegionArtifact {
        SealedStructuredRegionArtifact {
            authority: self.authority,
            root: self.root,
            nodes: self
                .nodes
                .into_iter()
                .map(|node| StructuredRegionNode {
                    parent: node.parent,
                    depth: node.depth,
                    entry: node.entry,
                    children: node.children.into_boxed_slice(),
                    emission_anchor: node.emission_anchor,
                    kind: node.kind,
                })
                .collect(),
        }
    }

    fn push_node(
        &mut self,
        parent: Option<RegionId>,
        depth: u32,
        entry: u64,
        kind: StructuredRegionKind,
    ) -> Result<RegionId, StructuredRegionBuildError> {
        let raw = u32::try_from(self.nodes.len())
            .map_err(|_| StructuredRegionBuildError::TooManyRegions)?;
        let id = RegionId(raw);
        self.nodes.push(DraftNode {
            parent,
            depth,
            entry,
            children: Vec::new(),
            emission_anchor: RegionEmissionAnchor(raw),
            kind,
        });
        Ok(id)
    }
}

fn kind_of(region: &Region) -> StructuredRegionKind {
    match region {
        Region::Block(_) => StructuredRegionKind::Block,
        Region::Sequence(_) => StructuredRegionKind::Sequence,
        Region::IfThenElse { .. } => StructuredRegionKind::IfThenElse,
        Region::WhileLoop { .. } => StructuredRegionKind::WhileLoop,
        Region::DoWhileLoop { .. } => StructuredRegionKind::DoWhileLoop,
        Region::MultiExit { .. } => StructuredRegionKind::MultiExit,
        Region::Transfer { .. } => StructuredRegionKind::Transfer,
        Region::Switch { .. } => StructuredRegionKind::Switch,
        Region::Irreducible { .. } => StructuredRegionKind::Irreducible,
    }
}

fn direct_children(region: &Region) -> Vec<&Region> {
    match region {
        Region::Block(_) | Region::Transfer { .. } | Region::Irreducible { .. } => Vec::new(),
        Region::Sequence(regions) => regions.iter().collect(),
        Region::IfThenElse {
            then_region,
            else_region,
            ..
        } => {
            let mut children = vec![then_region.as_ref()];
            if let Some(else_region) = else_region {
                children.push(else_region.as_ref());
            }
            children
        }
        Region::WhileLoop { body, .. }
        | Region::DoWhileLoop { body, .. }
        | Region::MultiExit { head: body, .. } => vec![body.as_ref()],
        Region::Switch { cases, default, .. } => {
            let mut children = cases
                .iter()
                .map(|(_, region)| region.as_ref())
                .collect::<Vec<_>>();
            if let Some(default) = default {
                children.push(default.as_ref());
            }
            children
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::region::RegionTransferKind;

    fn node_signature(
        artifact: &SealedStructuredRegionArtifact,
    ) -> Vec<(
        Option<usize>,
        u32,
        u64,
        Vec<usize>,
        usize,
        StructuredRegionKind,
    )> {
        artifact
            .nodes()
            .iter()
            .map(|node| {
                (
                    node.parent().map(RegionId::index),
                    node.depth(),
                    node.entry(),
                    node.children().iter().map(|id| id.index()).collect(),
                    node.emission_anchor().index(),
                    node.kind(),
                )
            })
            .collect()
    }

    #[test]
    fn raw_region_tree_seals_as_dense_deterministic_preorder() {
        let region = Region::Sequence(vec![
            Region::Block(0x1000),
            Region::IfThenElse {
                cond_block: 0x1010,
                then_region: Box::new(Region::Block(0x1020)),
                else_region: Some(Box::new(Region::WhileLoop {
                    header: 0x1030,
                    body: Box::new(Region::Block(0x1040)),
                })),
                merge_block: Some(0x1050),
            },
        ]);

        let first = StructuredRegionDraft::from_region(0x1000, &region)
            .expect("region draft")
            .seal();
        let second = StructuredRegionDraft::from_region(0x1000, &region)
            .expect("region draft")
            .seal();

        let expected = vec![
            (
                None,
                0,
                0x1000,
                vec![1],
                0,
                StructuredRegionKind::FunctionBody,
            ),
            (
                Some(0),
                1,
                0x1000,
                vec![2, 3],
                1,
                StructuredRegionKind::Sequence,
            ),
            (Some(1), 2, 0x1000, vec![], 2, StructuredRegionKind::Block),
            (
                Some(1),
                2,
                0x1010,
                vec![4, 5],
                3,
                StructuredRegionKind::IfThenElse,
            ),
            (Some(3), 3, 0x1020, vec![], 4, StructuredRegionKind::Block),
            (
                Some(3),
                3,
                0x1030,
                vec![6],
                5,
                StructuredRegionKind::WhileLoop,
            ),
            (Some(5), 4, 0x1040, vec![], 6, StructuredRegionKind::Block),
        ];
        assert_eq!(node_signature(&first), expected);
        assert_eq!(node_signature(&first), node_signature(&second));
        assert_eq!(first.root().index(), 0);
        for (index, node) in first.nodes().iter().enumerate() {
            let (id, resolved) = first
                .node_for_anchor(first.authority(), node.emission_anchor())
                .expect("dense anchor");
            assert_eq!(id.index(), index);
            assert!(std::ptr::eq(node, resolved));
        }
    }

    #[test]
    fn synthetic_appends_are_root_siblings_in_exact_emission_order() {
        let region = Region::Block(0x1000);
        let mut draft = StructuredRegionDraft::from_region(0x1000, &region).expect("region draft");
        let authority = draft.authority().clone();
        let (join, join_anchor) = draft
            .append_synthetic(SyntheticRegionKind::SharedJoin, 0x1040)
            .expect("shared join");
        let (exit, exit_anchor) = draft
            .append_synthetic(SyntheticRegionKind::DeferredSharedExit, 0x1080)
            .expect("shared exit");
        let sealed = draft.seal();

        assert_eq!(*sealed.authority(), authority);
        assert_eq!(
            sealed.node(sealed.root()).expect("root").children(),
            &[RegionId(1), join, exit]
        );
        assert_eq!(join.index(), 2);
        assert_eq!(join_anchor.index(), 2);
        assert_eq!(exit.index(), 3);
        assert_eq!(exit_anchor.index(), 3);
        assert_eq!(
            sealed.node(join).expect("join").parent(),
            Some(sealed.root())
        );
        assert_eq!(
            sealed.node(exit).expect("exit").parent(),
            Some(sealed.root())
        );
        assert_eq!(
            sealed.node(join).expect("join").kind(),
            StructuredRegionKind::Synthetic(SyntheticRegionKind::SharedJoin)
        );
        assert_eq!(
            sealed.node(exit).expect("exit").kind(),
            StructuredRegionKind::Synthetic(SyntheticRegionKind::DeferredSharedExit)
        );
    }

    #[test]
    fn transfer_occurrence_keeps_its_exact_region_entry_contract() {
        let region = Region::Transfer {
            loop_header: 0x1000,
            source: 0x1010,
            target: 0x1020,
            kind: RegionTransferKind::Exit,
        };
        let artifact = StructuredRegionDraft::from_region(0x1000, &region)
            .expect("region draft")
            .seal();
        let transfer = artifact.node(RegionId(1)).expect("transfer node");
        assert_eq!(transfer.entry(), region.entry());
        assert_eq!(transfer.kind(), StructuredRegionKind::Transfer);
    }

    #[test]
    fn independently_sealed_artifacts_never_share_authority() {
        let region = Region::Block(0x1000);
        let first = StructuredRegionDraft::from_region(0x1000, &region)
            .expect("first")
            .seal();
        let second = StructuredRegionDraft::from_region(0x1000, &region)
            .expect("second")
            .seal();
        assert_ne!(first.authority(), second.authority());
        assert!(
            first
                .node_for_anchor(second.authority(), RegionEmissionAnchor(0))
                .is_none()
        );
        assert_eq!(node_signature(&first), node_signature(&second));
    }
}
