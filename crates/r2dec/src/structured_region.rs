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

use std::sync::Arc;

use crate::ast::{CStmt, SwitchCase};
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
pub(crate) struct StructuredRegionArtifactAuthority {
    tree: Arc<()>,
    source: r2ssa::SsaArtifactAuthority,
}

impl StructuredRegionArtifactAuthority {
    fn new(source: &r2ssa::SsaArtifactAuthority) -> Self {
        Self {
            tree: Arc::new(()),
            source: source.clone(),
        }
    }

    fn matches_source(&self, source: &r2ssa::SsaArtifactAuthority) -> bool {
        &self.source == source
    }
}

impl std::fmt::Debug for StructuredRegionArtifactAuthority {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("StructuredRegionArtifactAuthority(..)")
    }
}

impl PartialEq for StructuredRegionArtifactAuthority {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.tree, &other.tree)
    }
}

impl Eq for StructuredRegionArtifactAuthority {}

impl std::hash::Hash for StructuredRegionArtifactAuthority {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&Arc::as_ptr(&self.tree), state);
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

/// Construction metadata carried by an exact statement occurrence.
///
/// `anchor` is empty while the structurer is still rewriting the statement
/// tree.  Sealing walks the final tree once in lexical preorder, assigns the
/// dense anchor, and builds the immutable artifact from that same walk.  The
/// marker and artifact therefore cannot disagree about occurrence identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredRegionMarker {
    entry: u64,
    kind: StructuredRegionKind,
    anchor: Option<RegionEmissionAnchor>,
    authority: Option<StructuredRegionArtifactAuthority>,
}

impl StructuredRegionMarker {
    pub(crate) const fn unsealed(entry: u64, kind: StructuredRegionKind) -> Self {
        Self {
            entry,
            kind,
            anchor: None,
            authority: None,
        }
    }

    pub(crate) const fn emission_anchor(&self) -> Option<RegionEmissionAnchor> {
        self.anchor
    }

    fn authority(&self) -> Option<&StructuredRegionArtifactAuthority> {
        self.authority.as_ref()
    }
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
    #[cfg(test)]
    children: Box<[RegionId]>,
    #[cfg(test)]
    emission_anchor: RegionEmissionAnchor,
    #[cfg(test)]
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

    #[cfg(test)]
    pub(crate) fn children(&self) -> &[RegionId] {
        &self.children
    }

    #[cfg(test)]
    pub(crate) const fn emission_anchor(&self) -> RegionEmissionAnchor {
        self.emission_anchor
    }

    #[cfg(test)]
    pub(crate) const fn kind(&self) -> StructuredRegionKind {
        self.kind
    }
}

/// Immutable lexical-region artifact consumed by placement and final emission.
#[derive(Debug, Clone)]
pub(crate) struct SealedStructuredRegionArtifact {
    authority: StructuredRegionArtifactAuthority,
    #[cfg(test)]
    root: RegionId,
    nodes: Box<[StructuredRegionNode]>,
}

impl SealedStructuredRegionArtifact {
    pub(crate) const fn authority(&self) -> &StructuredRegionArtifactAuthority {
        &self.authority
    }

    pub(crate) fn matches_source(&self, source: &r2ssa::SsaArtifactAuthority) -> bool {
        self.authority.matches_source(source)
    }

    #[cfg(test)]
    pub(crate) const fn root(&self) -> RegionId {
        self.root
    }

    /// Root of the analyzed tree below the explicit function-body scope.
    #[cfg(test)]
    pub(crate) fn source_root(&self) -> RegionId {
        self.nodes[self.root.index()].children[0]
    }

    /// Children already retained for `id`, in exact render order.
    #[cfg(test)]
    pub(crate) fn children(&self, id: RegionId) -> Option<&[RegionId]> {
        self.nodes
            .get(id.index())
            .map(|node| node.children.as_ref())
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

    /// Resolve one marker only when it was sealed by this exact artifact.
    ///
    /// The dense anchor is deliberately insufficient by itself: independent
    /// artifacts reuse the same small integer domain.  Consumers of a final
    /// marker tree must carry the run-local authority minted with the marker.
    pub(crate) fn node_for_marker(
        &self,
        marker: &StructuredRegionMarker,
    ) -> Option<(RegionId, &StructuredRegionNode)> {
        let authority = marker.authority()?;
        let anchor = marker.emission_anchor()?;
        self.node_for_anchor(authority, anchor)
    }
}

/// Failure to retain a region tree without truncating a dense identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StructuredRegionBuildError {
    TooManyRegions,
    RegionDepthOverflow,
    MissingFunctionBodyMarker,
    NestedFunctionBodyMarker,
    MarkerAlreadySealed,
    MissingSourceAuthority,
}

/// Final marker tree no longer matches the artifact sealed from it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StructuredRegionFinalizationError {
    UnsealedMarker,
    ForeignMarker {
        anchor: RegionEmissionAnchor,
    },
    DuplicateMarker {
        region: RegionId,
    },
    MissingMarker {
        region: RegionId,
    },
    ParentMismatch {
        region: RegionId,
    },
    OutOfOrder {
        region: RegionId,
        expected: RegionId,
    },
}

/// Validate and remove region markers at the final emission boundary.
pub(crate) fn strip_final_region_markers(
    statements: &mut [CStmt],
    regions: &SealedStructuredRegionArtifact,
) -> Result<(), StructuredRegionFinalizationError> {
    validate_final_region_marker_tree(statements, regions)?;
    statements.iter_mut().for_each(strip_region_markers);
    Ok(())
}

/// Check that every final marker still belongs to this exact sealed tree.
pub(crate) fn validate_final_region_marker_tree(
    statements: &[CStmt],
    regions: &SealedStructuredRegionArtifact,
) -> Result<(), StructuredRegionFinalizationError> {
    let mut seen = vec![false; regions.nodes().len()];
    let mut next_preorder = 0usize;
    for statement in statements {
        validate_final_region_markers(statement, regions, None, &mut seen, &mut next_preorder)?;
    }
    if let Some(index) = seen.iter().position(|seen| !seen) {
        return Err(StructuredRegionFinalizationError::MissingMarker {
            region: RegionId(index as u32),
        });
    }
    Ok(())
}

fn validate_final_region_markers(
    statement: &CStmt,
    regions: &SealedStructuredRegionArtifact,
    parent: Option<RegionId>,
    seen: &mut [bool],
    next_preorder: &mut usize,
) -> Result<(), StructuredRegionFinalizationError> {
    if let CStmt::StructuredRegion { marker, stmt } = statement {
        let anchor = marker
            .emission_anchor()
            .ok_or(StructuredRegionFinalizationError::UnsealedMarker)?;
        let (region, node) = regions
            .node_for_marker(marker)
            .ok_or(StructuredRegionFinalizationError::ForeignMarker { anchor })?;
        if std::mem::replace(&mut seen[region.index()], true) {
            return Err(StructuredRegionFinalizationError::DuplicateMarker { region });
        }
        if node.parent() != parent {
            return Err(StructuredRegionFinalizationError::ParentMismatch { region });
        }
        let expected = RegionId(
            u32::try_from(*next_preorder)
                .expect("a validated dense region domain already fits RegionId"),
        );
        if region != expected {
            return Err(StructuredRegionFinalizationError::OutOfOrder { region, expected });
        }
        *next_preorder += 1;
        return validate_final_region_markers(stmt, regions, Some(region), seen, next_preorder);
    }
    if let CStmt::Observed { stmt, .. } = statement {
        return validate_final_region_markers(stmt, regions, parent, seen, next_preorder);
    }
    match statement {
        CStmt::StructuredRegion { .. } | CStmt::Observed { .. } => {
            unreachable!("leading wrappers handled above")
        }
        CStmt::Block(statements) => {
            for statement in statements {
                validate_final_region_markers(statement, regions, parent, seen, next_preorder)?;
            }
        }
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            validate_final_region_markers(then_body, regions, parent, seen, next_preorder)?;
            if let Some(else_body) = else_body {
                validate_final_region_markers(else_body, regions, parent, seen, next_preorder)?;
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            validate_final_region_markers(body, regions, parent, seen, next_preorder)?
        }
        CStmt::For { init, body, .. } => {
            if let Some(init) = init {
                validate_final_region_markers(init, regions, parent, seen, next_preorder)?;
            }
            validate_final_region_markers(body, regions, parent, seen, next_preorder)?;
        }
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                for statement in &case.body {
                    validate_final_region_markers(statement, regions, parent, seen, next_preorder)?;
                }
            }
            if let Some(default) = default {
                for statement in default {
                    validate_final_region_markers(statement, regions, parent, seen, next_preorder)?;
                }
            }
        }
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Decl { .. }
        | CStmt::Return(_)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
    Ok(())
}

#[derive(Debug)]
struct DraftNode {
    parent: Option<RegionId>,
    depth: u32,
    entry: u64,
    #[cfg(test)]
    children: Vec<RegionId>,
    emission_anchor: RegionEmissionAnchor,
    #[cfg(test)]
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
    #[cfg(test)]
    root: RegionId,
    nodes: Vec<DraftNode>,
}

impl StructuredRegionDraft {
    /// Retain one analyzed region tree in deterministic render preorder.
    #[cfg(test)]
    pub(crate) fn from_region(
        function_entry: u64,
        region: &Region,
    ) -> Result<Self, StructuredRegionBuildError> {
        let source = test_source_authority();
        let mut draft = Self {
            authority: StructuredRegionArtifactAuthority::new(&source),
            #[cfg(test)]
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

    #[cfg(test)]
    pub(crate) const fn authority(&self) -> &StructuredRegionArtifactAuthority {
        &self.authority
    }

    /// Anchor that the structurer must attach to the emitted occurrence.
    pub(crate) fn emission_anchor(&self, id: RegionId) -> Option<RegionEmissionAnchor> {
        self.nodes.get(id.index()).map(|node| node.emission_anchor)
    }

    /// Record one root-level statement appended after the analyzed region.
    #[cfg(test)]
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
            #[cfg(test)]
            root: self.root,
            nodes: self
                .nodes
                .into_iter()
                .map(|node| StructuredRegionNode {
                    parent: node.parent,
                    depth: node.depth,
                    entry: node.entry,
                    #[cfg(test)]
                    children: node.children.into_boxed_slice(),
                    #[cfg(test)]
                    emission_anchor: node.emission_anchor,
                    #[cfg(test)]
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
        _kind: StructuredRegionKind,
    ) -> Result<RegionId, StructuredRegionBuildError> {
        let raw = u32::try_from(self.nodes.len())
            .map_err(|_| StructuredRegionBuildError::TooManyRegions)?;
        let id = RegionId(raw);
        self.nodes.push(DraftNode {
            parent,
            depth,
            entry,
            #[cfg(test)]
            children: Vec::new(),
            emission_anchor: RegionEmissionAnchor(raw),
            #[cfg(test)]
            kind: _kind,
        });
        Ok(id)
    }
}

/// A structured statement tree and the region artifact sealed from the same
/// exact occurrences.
pub(crate) struct SealedStructuredBody {
    stmt: CStmt,
    regions: SealedStructuredRegionArtifact,
}

impl SealedStructuredBody {
    pub(crate) fn regions(&self) -> &SealedStructuredRegionArtifact {
        &self.regions
    }

    #[cfg(test)]
    pub(crate) fn into_stmt(mut self) -> CStmt {
        strip_region_markers(&mut self.stmt);
        self.stmt
    }

    /// Transfer the still-marked tree and its sole lexical authority together.
    ///
    /// Production finalization carries both parts through every late AST
    /// rewrite, derives placement from the rewritten marker tree, and strips
    /// markers only at the emission boundary.
    pub(crate) fn into_marked_parts(self) -> (CStmt, SealedStructuredRegionArtifact) {
        (self.stmt, self.regions)
    }

    /// Visit every exact emitted region occurrence in lexical preorder.
    ///
    /// Consumers receive both the canonical artifact node and the semantic
    /// statement it owns.  They never need to match the internal AST wrapper.
    pub(crate) fn visit_occurrences(&self, mut visit: impl FnMut(StructuredRegionOccurrence<'_>)) {
        visit_occurrences(
            &self.stmt,
            &self.regions,
            self.regions.authority(),
            &mut visit,
        );
    }

    /// Visit semantic statement occurrences with their exact innermost region.
    ///
    /// Region wrappers are consumed here, not exposed to callers. Observation
    /// chains remain intact on `stmt`, and each semantic statement position is
    /// reported once. This is the bridge final occurrence collectors use; they
    /// do not need an ad hoc AST matcher for lexical markers.
    #[cfg(test)]
    pub(crate) fn visit_scoped_statements(
        &self,
        mut visit: impl FnMut(ScopedStructuredStatement<'_>),
    ) {
        visit_scoped_stmt(
            &self.stmt,
            None,
            &self.regions,
            self.regions.authority(),
            &mut visit,
        );
    }
}

/// Borrowed view of one exact emitted lexical occurrence.
pub(crate) struct StructuredRegionOccurrence<'a> {
    #[cfg(test)]
    id: RegionId,
    #[cfg(test)]
    anchor: RegionEmissionAnchor,
    #[cfg(test)]
    node: &'a StructuredRegionNode,
    #[cfg(test)]
    stmt: &'a CStmt,
    #[cfg(not(test))]
    _marker: std::marker::PhantomData<&'a ()>,
}

impl<'a> StructuredRegionOccurrence<'a> {
    #[cfg(test)]
    pub(crate) const fn id(&self) -> RegionId {
        self.id
    }

    #[cfg(test)]
    pub(crate) const fn anchor(&self) -> RegionEmissionAnchor {
        self.anchor
    }

    #[cfg(test)]
    pub(crate) const fn node(&self) -> &'a StructuredRegionNode {
        self.node
    }

    #[cfg(test)]
    pub(crate) const fn stmt(&self) -> &'a CStmt {
        self.stmt
    }
}

/// One semantic statement occurrence paired with its exact lexical region.
#[cfg(test)]
pub(crate) struct ScopedStructuredStatement<'a> {
    region: RegionId,
    anchor: RegionEmissionAnchor,
    node: &'a StructuredRegionNode,
    stmt: &'a CStmt,
}

#[cfg(test)]
impl<'a> ScopedStructuredStatement<'a> {
    pub(crate) const fn region(&self) -> RegionId {
        self.region
    }

    pub(crate) const fn anchor(&self) -> RegionEmissionAnchor {
        self.anchor
    }

    pub(crate) const fn node(&self) -> &'a StructuredRegionNode {
        self.node
    }

    pub(crate) const fn stmt(&self) -> &'a CStmt {
        self.stmt
    }
}

/// Seal exact region markers after all structurer-local shape rewrites.
pub(crate) fn seal_structured_body(
    mut stmt: CStmt,
    source: &r2ssa::SsaArtifactAuthority,
) -> Result<SealedStructuredBody, StructuredRegionBuildError> {
    let CStmt::StructuredRegion {
        marker: root_marker,
        stmt: root_stmt,
    } = &mut stmt
    else {
        return Err(StructuredRegionBuildError::MissingFunctionBodyMarker);
    };
    if root_marker.kind != StructuredRegionKind::FunctionBody {
        return Err(StructuredRegionBuildError::MissingFunctionBodyMarker);
    }
    if root_marker.anchor.is_some() || root_marker.authority.is_some() {
        return Err(StructuredRegionBuildError::MarkerAlreadySealed);
    }

    let mut draft = StructuredRegionDraft {
        authority: StructuredRegionArtifactAuthority::new(source),
        #[cfg(test)]
        root: RegionId(0),
        nodes: Vec::new(),
    };
    let root = draft.push_node(
        None,
        0,
        root_marker.entry,
        StructuredRegionKind::FunctionBody,
    )?;
    #[cfg(test)]
    debug_assert_eq!(root, draft.root);
    root_marker.anchor = draft.emission_anchor(root);
    root_marker.authority = Some(draft.authority.clone());
    seal_stmt_children(root_stmt, root, &mut draft)?;
    let regions = draft.seal();
    Ok(SealedStructuredBody { stmt, regions })
}

#[cfg(test)]
pub(crate) fn seal_structured_body_for_test(
    stmt: CStmt,
) -> Result<SealedStructuredBody, StructuredRegionBuildError> {
    let source = test_source_authority();
    seal_structured_body(stmt, &source)
}

#[cfg(test)]
fn test_source_authority() -> r2ssa::SsaArtifactAuthority {
    let mut block = r2il::R2ILBlock::new(0x1000, 1);
    block.push(r2il::R2ILOp::Return {
        target: r2il::Varnode::constant(0, 8),
    });
    r2ssa::SsaArtifact::raw(&[block], None)
        .expect("test source artifact")
        .authority()
        .clone()
}

fn seal_stmt_children(
    stmt: &mut CStmt,
    parent: RegionId,
    draft: &mut StructuredRegionDraft,
) -> Result<(), StructuredRegionBuildError> {
    match stmt {
        CStmt::StructuredRegion { marker, stmt } => {
            if marker.anchor.is_some() || marker.authority.is_some() {
                return Err(StructuredRegionBuildError::MarkerAlreadySealed);
            }
            if marker.kind == StructuredRegionKind::FunctionBody {
                return Err(StructuredRegionBuildError::NestedFunctionBodyMarker);
            }
            let depth = draft.nodes[parent.index()]
                .depth
                .checked_add(1)
                .ok_or(StructuredRegionBuildError::RegionDepthOverflow)?;
            let id = draft.push_node(Some(parent), depth, marker.entry, marker.kind)?;
            #[cfg(test)]
            draft.nodes[parent.index()].children.push(id);
            marker.anchor = draft.emission_anchor(id);
            marker.authority = Some(draft.authority.clone());
            seal_stmt_children(stmt, id, draft)
        }
        CStmt::Observed { stmt, .. } => seal_stmt_children(stmt, parent, draft),
        CStmt::Block(stmts) => {
            for stmt in stmts {
                seal_stmt_children(stmt, parent, draft)?;
            }
            Ok(())
        }
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            seal_stmt_children(then_body, parent, draft)?;
            if let Some(else_body) = else_body {
                seal_stmt_children(else_body, parent, draft)?;
            }
            Ok(())
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            seal_stmt_children(body, parent, draft)
        }
        CStmt::For { init, body, .. } => {
            if let Some(init) = init {
                seal_stmt_children(init, parent, draft)?;
            }
            seal_stmt_children(body, parent, draft)
        }
        CStmt::Switch { cases, default, .. } => {
            for SwitchCase { body, .. } in cases {
                for stmt in body {
                    seal_stmt_children(stmt, parent, draft)?;
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    seal_stmt_children(stmt, parent, draft)?;
                }
            }
            Ok(())
        }
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Decl { .. }
        | CStmt::Return(_)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => Ok(()),
    }
}

fn visit_occurrences<'a>(
    stmt: &'a CStmt,
    regions: &'a SealedStructuredRegionArtifact,
    authority: &StructuredRegionArtifactAuthority,
    visit: &mut impl FnMut(StructuredRegionOccurrence<'a>),
) {
    match stmt {
        CStmt::StructuredRegion { marker, stmt } => {
            let _anchor = marker
                .emission_anchor()
                .expect("sealed body contains only sealed region markers");
            let (_id, _node) = regions
                .node_for_marker(marker)
                .expect("sealed marker belongs to its structured-region artifact");
            visit(StructuredRegionOccurrence {
                #[cfg(test)]
                id: _id,
                #[cfg(test)]
                anchor: _anchor,
                #[cfg(test)]
                node: _node,
                #[cfg(test)]
                stmt,
                #[cfg(not(test))]
                _marker: std::marker::PhantomData,
            });
            visit_occurrences(stmt, regions, authority, visit);
        }
        CStmt::Observed { stmt, .. } => visit_occurrences(stmt, regions, authority, visit),
        CStmt::Block(stmts) => {
            for stmt in stmts {
                visit_occurrences(stmt, regions, authority, visit);
            }
        }
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            visit_occurrences(then_body, regions, authority, visit);
            if let Some(else_body) = else_body {
                visit_occurrences(else_body, regions, authority, visit);
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            visit_occurrences(body, regions, authority, visit)
        }
        CStmt::For { init, body, .. } => {
            if let Some(init) = init {
                visit_occurrences(init, regions, authority, visit);
            }
            visit_occurrences(body, regions, authority, visit);
        }
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                for stmt in &case.body {
                    visit_occurrences(stmt, regions, authority, visit);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    visit_occurrences(stmt, regions, authority, visit);
                }
            }
        }
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Decl { .. }
        | CStmt::Return(_)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
}

#[cfg(test)]
fn visit_scoped_stmt<'a>(
    stmt: &'a CStmt,
    current: Option<(RegionId, RegionEmissionAnchor)>,
    regions: &'a SealedStructuredRegionArtifact,
    authority: &StructuredRegionArtifactAuthority,
    visit: &mut impl FnMut(ScopedStructuredStatement<'a>),
) {
    if let CStmt::StructuredRegion { marker, stmt } = stmt {
        let anchor = marker
            .emission_anchor()
            .expect("sealed body contains only sealed region markers");
        let (id, _) = regions
            .node_for_marker(marker)
            .expect("sealed marker belongs to its structured-region artifact");
        visit_scoped_stmt(stmt, Some((id, anchor)), regions, authority, visit);
        return;
    }

    if let Some((region, _anchor)) = current {
        let _node = regions
            .node(region)
            .expect("scoped statement region belongs to its artifact");
        visit(ScopedStructuredStatement {
            region,
            anchor: _anchor,
            node: _node,
            stmt,
        });
    }

    // Leading observation wrappers are one statement occurrence. Recurse into
    // child statements of the semantic node, not through the wrapper as a
    // second occurrence.
    let semantic = stmt.unobserved();
    match semantic {
        CStmt::StructuredRegion { .. } => {
            visit_scoped_stmt(semantic, current, regions, authority, visit)
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                visit_scoped_stmt(stmt, current, regions, authority, visit);
            }
        }
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            visit_scoped_stmt(then_body, current, regions, authority, visit);
            if let Some(else_body) = else_body {
                visit_scoped_stmt(else_body, current, regions, authority, visit);
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            visit_scoped_stmt(body, current, regions, authority, visit)
        }
        CStmt::For { init, body, .. } => {
            if let Some(init) = init {
                visit_scoped_stmt(init, current, regions, authority, visit);
            }
            visit_scoped_stmt(body, current, regions, authority, visit)
        }
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                for stmt in &case.body {
                    visit_scoped_stmt(stmt, current, regions, authority, visit);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    visit_scoped_stmt(stmt, current, regions, authority, visit);
                }
            }
        }
        CStmt::Observed { .. } => unreachable!("leading observations were unwrapped"),
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Decl { .. }
        | CStmt::Return(_)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
}

fn strip_region_markers(stmt: &mut CStmt) {
    while let CStmt::StructuredRegion { stmt: inner, .. } = stmt {
        *stmt = std::mem::replace(inner.as_mut(), CStmt::Empty);
    }
    match stmt {
        CStmt::Observed { stmt, .. } => strip_region_markers(stmt),
        CStmt::Block(stmts) => stmts.iter_mut().for_each(strip_region_markers),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            strip_region_markers(then_body);
            if let Some(else_body) = else_body {
                strip_region_markers(else_body);
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => strip_region_markers(body),
        CStmt::For { init, body, .. } => {
            if let Some(init) = init {
                strip_region_markers(init);
            }
            strip_region_markers(body);
        }
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                case.body.iter_mut().for_each(strip_region_markers);
            }
            if let Some(default) = default {
                default.iter_mut().for_each(strip_region_markers);
            }
        }
        CStmt::StructuredRegion { .. } => unreachable!("leading region markers were stripped"),
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Decl { .. }
        | CStmt::Return(_)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
}

pub(crate) fn kind_of(region: &Region) -> StructuredRegionKind {
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

#[cfg(test)]
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
    use super::seal_structured_body_for_test as seal_structured_body;
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

    #[test]
    fn sealed_artifact_retains_the_exact_ssa_source_authority() {
        let first_source = test_source_authority();
        let second_source = test_source_authority();
        let sealed = super::seal_structured_body(
            CStmt::structured_region(
                StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
                CStmt::Empty,
            ),
            &first_source,
        )
        .expect("source-bound region artifact");

        assert!(sealed.regions().matches_source(&first_source));
        assert!(!sealed.regions().matches_source(&second_source));
    }

    #[test]
    fn final_tree_rejects_same_index_markers_from_another_artifact() {
        let local = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::structured_region(
                StructuredRegionMarker::unsealed(0x1010, StructuredRegionKind::Block),
                CStmt::Empty,
            ),
        ))
        .expect("local artifact");
        let foreign = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x2000, StructuredRegionKind::FunctionBody),
            CStmt::structured_region(
                StructuredRegionMarker::unsealed(0x2010, StructuredRegionKind::Block),
                CStmt::Empty,
            ),
        ))
        .expect("foreign artifact");
        let (_, local_regions) = local.into_marked_parts();
        let (foreign_stmt, _) = foreign.into_marked_parts();

        assert!(matches!(
            validate_final_region_marker_tree(&[foreign_stmt], &local_regions),
            Err(StructuredRegionFinalizationError::ForeignMarker { anchor })
                if anchor.index() == 0
        ));
    }

    #[test]
    fn final_tree_rejects_reparented_sealed_marker() {
        let sealed = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::structured_region(
                StructuredRegionMarker::unsealed(0x1010, StructuredRegionKind::Sequence),
                CStmt::structured_region(
                    StructuredRegionMarker::unsealed(0x1020, StructuredRegionKind::Block),
                    CStmt::Empty,
                ),
            ),
        ))
        .expect("nested artifact");
        let (stmt, regions) = sealed.into_marked_parts();
        let CStmt::StructuredRegion {
            marker: root_marker,
            stmt: sequence,
        } = stmt
        else {
            panic!("root marker")
        };
        let CStmt::StructuredRegion {
            marker: sequence_marker,
            stmt: child,
        } = *sequence
        else {
            panic!("sequence marker")
        };
        let CStmt::StructuredRegion {
            marker: child_marker,
            stmt: child_body,
        } = *child
        else {
            panic!("child marker")
        };
        let reparented = CStmt::structured_region(
            root_marker,
            CStmt::Block(vec![
                CStmt::structured_region(sequence_marker, CStmt::Empty),
                CStmt::structured_region(child_marker, *child_body),
            ]),
        );

        assert!(matches!(
            validate_final_region_marker_tree(&[reparented], &regions),
            Err(StructuredRegionFinalizationError::ParentMismatch { region })
                if region.index() == 2
        ));
    }

    #[test]
    fn sealed_body_visits_the_exact_statement_owned_by_each_anchor() {
        let first = CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1010, StructuredRegionKind::Block),
            CStmt::Comment("first".to_string()),
        );
        let second = CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1010, StructuredRegionKind::Block),
            CStmt::Comment("second".to_string()),
        );
        let body = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::Block(vec![first, second]),
        ))
        .expect("exact occurrence tree");

        let mut visited = Vec::new();
        body.visit_occurrences(|occurrence| {
            visited.push((
                occurrence.id().index(),
                occurrence.anchor().index(),
                occurrence.node().entry(),
                occurrence.stmt().clone_without_render_observations(),
            ));
        });

        assert_eq!(visited.len(), 3);
        assert_eq!(visited[0].0, 0);
        assert_eq!(visited[0].1, 0);
        assert_eq!(visited[1].2, 0x1010);
        assert_eq!(visited[2].2, 0x1010);
        assert_ne!(visited[1].0, visited[2].0);
        assert_ne!(visited[1].1, visited[2].1);
        assert_eq!(visited[1].3, CStmt::Comment("first".to_string()));
        assert_eq!(visited[2].3, CStmt::Comment("second".to_string()));

        let mut scoped_comments = Vec::new();
        body.visit_scoped_statements(|scoped| {
            if let CStmt::Comment(text) = scoped.stmt().unobserved() {
                scoped_comments.push((
                    scoped.region().index(),
                    scoped.anchor().index(),
                    scoped.node().entry(),
                    text.clone(),
                ));
            }
        });
        assert_eq!(
            scoped_comments,
            vec![
                (visited[1].0, visited[1].1, 0x1010, "first".to_string()),
                (visited[2].0, visited[2].1, 0x1010, "second".to_string()),
            ]
        );
    }

    #[test]
    fn sealed_body_keeps_synthetic_appends_as_function_body_children() {
        let source = CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::Block),
            CStmt::Comment("source".to_string()),
        );
        let join = CStmt::structured_region(
            StructuredRegionMarker::unsealed(
                0x1040,
                StructuredRegionKind::Synthetic(SyntheticRegionKind::SharedJoin),
            ),
            CStmt::Comment("join".to_string()),
        );
        let exit = CStmt::structured_region(
            StructuredRegionMarker::unsealed(
                0x1080,
                StructuredRegionKind::Synthetic(SyntheticRegionKind::DeferredSharedExit),
            ),
            CStmt::Comment("exit".to_string()),
        );
        let body = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::Block(vec![source, join, exit]),
        ))
        .expect("synthetic occurrence tree");

        let children = body
            .regions()
            .children(body.regions().root())
            .expect("function-body children");
        assert_eq!(children.len(), 3);
        assert_eq!(
            body.regions().node(children[1]).expect("join").kind(),
            StructuredRegionKind::Synthetic(SyntheticRegionKind::SharedJoin)
        );
        assert_eq!(
            body.regions().node(children[2]).expect("exit").kind(),
            StructuredRegionKind::Synthetic(SyntheticRegionKind::DeferredSharedExit)
        );
    }
}
