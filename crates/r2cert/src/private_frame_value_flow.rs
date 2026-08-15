//! Exact MemorySSA value-flow proofs for source-owned private frame regions.
//!
//! These witnesses do not create locals, types, statements, expressions, or
//! ledger dispositions. They only seal the already-certified memory statements
//! and exact MemorySSA version path belonging to one private stack interval.

use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    InstId, MemoryDefFact, MemoryLocation, MemorySSAFacts, MemoryUseFact, MemoryVersion, ObjectId,
    ObjectKind, RelativeMemoryAddress, SsaArtifact, StructuredAccessId, StructuredMemoryAccessFact,
};
use serde::{Serialize, Serializer};

use super::{
    CERTIFICATION_SCHEMA_VERSION, CertifiedArtifactOrigin, CertifiedMemoryStatement,
    CertifiedMemoryStatementKind, CertifiedNormalizedStackRange, CertifiedPrivateStackRegion,
    CertifiedSourceTopology, CertifiedStackDiscipline, MachineAddressSpace, ObligationLedger,
    frame_instruction_dominates, frame_statement_is_ledgered,
};

fn serialize_memory_version<S>(value: &MemoryVersion, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    (value.object, value.version).serialize(serializer)
}

/// Exact load and the nonzero MemorySSA version reaching it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameLoad {
    statement: CertifiedMemoryStatement,
    #[serde(serialize_with = "serialize_memory_version")]
    version: MemoryVersion,
}

impl CertifiedPrivateFrameLoad {
    pub const fn statement(&self) -> &CertifiedMemoryStatement {
        &self.statement
    }

    pub const fn version(&self) -> MemoryVersion {
        self.version
    }
}

/// Exact private-frame store definition retained by MemorySSA.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameStore {
    statement: CertifiedMemoryStatement,
    #[serde(serialize_with = "serialize_memory_version")]
    previous_version: MemoryVersion,
    #[serde(serialize_with = "serialize_memory_version")]
    next_version: MemoryVersion,
}

impl CertifiedPrivateFrameStore {
    pub const fn statement(&self) -> &CertifiedMemoryStatement {
        &self.statement
    }

    pub const fn previous_version(&self) -> MemoryVersion {
        self.previous_version
    }

    pub const fn next_version(&self) -> MemoryVersion {
        self.next_version
    }
}

/// One exact predecessor/version edge of a private-frame MemorySSA phi.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFramePhiInput {
    predecessor: u64,
    #[serde(serialize_with = "serialize_memory_version")]
    version: MemoryVersion,
}

impl CertifiedPrivateFramePhiInput {
    pub const fn predecessor(&self) -> u64 {
        self.predecessor
    }

    pub const fn version(&self) -> MemoryVersion {
        self.version
    }
}

/// Exact topology-bound MemorySSA join for one private-frame interval.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFramePhi {
    block_addr: u64,
    #[serde(serialize_with = "serialize_memory_version")]
    output_version: MemoryVersion,
    inputs: Box<[CertifiedPrivateFramePhiInput]>,
}

impl CertifiedPrivateFramePhi {
    pub const fn block_addr(&self) -> u64 {
        self.block_addr
    }

    pub const fn output_version(&self) -> MemoryVersion {
        self.output_version
    }

    pub const fn inputs(&self) -> &[CertifiedPrivateFramePhiInput] {
        &self.inputs
    }
}

/// Unique definition of one nonzero version retained by a value-flow proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedPrivateFrameVersionDefinition {
    Store(CertifiedPrivateFrameStore),
    Phi(CertifiedPrivateFramePhi),
}

impl CertifiedPrivateFrameVersionDefinition {
    pub const fn output_version(&self) -> MemoryVersion {
        match self {
            Self::Store(store) => store.next_version(),
            Self::Phi(phi) => phi.output_version(),
        }
    }

    pub const fn store(&self) -> Option<&CertifiedPrivateFrameStore> {
        match self {
            Self::Store(store) => Some(store),
            Self::Phi(_) => None,
        }
    }

    pub const fn phi(&self) -> Option<&CertifiedPrivateFramePhi> {
        match self {
            Self::Store(_) => None,
            Self::Phi(phi) => Some(phi),
        }
    }
}

/// Sealed, source-owned path from exact private-frame stores through optional
/// MemorySSA joins to one exact load.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedPrivateFrameValueFlow {
    schema_version: u32,
    origin: CertifiedArtifactOrigin,
    region: CertifiedPrivateStackRegion,
    object: ObjectId,
    range: CertifiedNormalizedStackRange,
    load: CertifiedPrivateFrameLoad,
    #[serde(serialize_with = "serialize_memory_version")]
    root_version: MemoryVersion,
    definitions: Box<[CertifiedPrivateFrameVersionDefinition]>,
}

impl CertifiedPrivateFrameValueFlow {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn region(&self) -> &CertifiedPrivateStackRegion {
        &self.region
    }

    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn range(&self) -> CertifiedNormalizedStackRange {
        self.range
    }

    pub const fn load(&self) -> &CertifiedPrivateFrameLoad {
        &self.load
    }

    pub const fn root_version(&self) -> MemoryVersion {
        self.root_version
    }

    /// Definitions are ordered by their exact `(object, version)` identity.
    pub const fn definitions(&self) -> &[CertifiedPrivateFrameVersionDefinition] {
        &self.definitions
    }

    pub fn definition(
        &self,
        version: MemoryVersion,
    ) -> Option<&CertifiedPrivateFrameVersionDefinition> {
        self.definitions
            .binary_search_by_key(&version, |definition| definition.output_version())
            .ok()
            .map(|index| &self.definitions[index])
    }
}

#[derive(Debug, Clone)]
struct ExactRegionFacts {
    object: ObjectId,
    range: CertifiedNormalizedStackRange,
    stores: BTreeMap<InstId, CertifiedPrivateFrameStore>,
    loads: BTreeMap<StructuredAccessId, CertifiedPrivateFrameLoad>,
    phis: Vec<CertifiedPrivateFramePhi>,
}

struct ExactMemoryStateReplay<'a> {
    artifact: &'a SsaArtifact,
    topology: &'a CertifiedSourceTopology,
    object: ObjectId,
    loads: BTreeMap<InstId, &'a CertifiedPrivateFrameLoad>,
    stores: &'a BTreeMap<InstId, CertifiedPrivateFrameStore>,
    phis: BTreeMap<u64, &'a CertifiedPrivateFramePhi>,
    visiting: BTreeSet<u64>,
    outgoing: BTreeMap<u64, MemoryVersion>,
    consumed_loads: BTreeSet<InstId>,
    consumed_stores: BTreeSet<InstId>,
    consumed_phis: BTreeSet<u64>,
}

impl ExactMemoryStateReplay<'_> {
    fn zero(&self) -> MemoryVersion {
        MemoryVersion {
            object: self.object,
            version: 0,
        }
    }

    fn replay_block(&mut self, block_addr: u64) -> Option<MemoryVersion> {
        if let Some(version) = self.outgoing.get(&block_addr) {
            return Some(*version);
        }
        if !self.visiting.insert(block_addr) {
            return None;
        }
        let source_block = self.topology.block(block_addr)?;
        let predecessors = source_block.predecessors().to_vec();
        if block_addr == self.topology.entry_addr() {
            if !predecessors.is_empty() {
                return None;
            }
        } else if predecessors.is_empty() {
            return None;
        }
        let incoming = predecessors
            .iter()
            .map(|predecessor| {
                self.replay_block(*predecessor)
                    .map(|version| (*predecessor, version))
            })
            .collect::<Option<Vec<_>>>()?;
        let mut current =
            if incoming.is_empty() {
                if self.phis.contains_key(&block_addr) {
                    return None;
                }
                self.zero()
            } else {
                let first = incoming[0].1;
                if incoming.iter().all(|(_, version)| *version == first) {
                    if self.phis.contains_key(&block_addr) {
                        return None;
                    }
                    first
                } else {
                    let phi = *self.phis.get(&block_addr)?;
                    if phi.inputs().len() != incoming.len()
                        || !phi.inputs().iter().zip(&incoming).all(
                            |(input, (predecessor, version))| {
                                input.predecessor() == *predecessor && input.version() == *version
                            },
                        )
                        || !self.consumed_phis.insert(block_addr)
                    {
                        return None;
                    }
                    phi.output_version()
                }
            };
        let graph = self.artifact.graph();
        let graph_block = graph.block(*graph.block_by_addr.get(&block_addr)?)?;
        let graph_predecessors = graph_block
            .predecessors
            .iter()
            .map(|predecessor| graph.block(*predecessor).map(|block| block.addr))
            .collect::<Option<Vec<_>>>()?;
        if graph_predecessors != predecessors {
            return None;
        }
        for inst_id in &graph_block.insts {
            if let Some(load) = self.loads.get(inst_id) {
                if load.version() != current || !self.consumed_loads.insert(*inst_id) {
                    return None;
                }
            }
            if let Some(store) = self.stores.get(inst_id) {
                if store.previous_version() != current
                    || store.next_version().object != self.object
                    || store.next_version().version == 0
                    || !self.consumed_stores.insert(*inst_id)
                {
                    return None;
                }
                current = store.next_version();
            }
        }
        self.visiting.remove(&block_addr);
        self.outgoing.insert(block_addr, current);
        Some(current)
    }
}

fn exact_memory_state_replays(
    artifact: &SsaArtifact,
    topology: &CertifiedSourceTopology,
    facts: &ExactRegionFacts,
) -> bool {
    let mut loads = BTreeMap::new();
    for load in facts.loads.values() {
        if loads.insert(load.statement().access().inst, load).is_some() {
            return false;
        }
    }
    let mut phis = BTreeMap::new();
    for phi in &facts.phis {
        if phis.insert(phi.block_addr(), phi).is_some() {
            return false;
        }
    }
    let mut replay = ExactMemoryStateReplay {
        artifact,
        topology,
        object: facts.object,
        loads,
        stores: &facts.stores,
        phis,
        visiting: BTreeSet::new(),
        outgoing: BTreeMap::new(),
        consumed_loads: BTreeSet::new(),
        consumed_stores: BTreeSet::new(),
        consumed_phis: BTreeSet::new(),
    };
    if topology
        .blocks()
        .iter()
        .any(|block| replay.replay_block(block.addr()).is_none())
    {
        return false;
    }
    replay.consumed_loads.len() == facts.loads.len()
        && replay.consumed_stores.len() == facts.stores.len()
        && replay.consumed_phis.len() == facts.phis.len()
}

fn artifact_matches_origin(artifact: &SsaArtifact, origin: &CertifiedArtifactOrigin) -> bool {
    origin.is_valid()
        && origin.authority.artifact.as_ref() == Some(artifact.authority())
        && origin.source() == artifact.obligations()
}

fn exact_location(object: ObjectId, size: u32) -> MemoryLocation {
    MemoryLocation {
        space: r2il::SpaceId::Ram,
        object,
        address: RelativeMemoryAddress::Exact(0),
        size,
    }
}

fn exact_use(memory: &MemorySSAFacts, inst: InstId) -> Option<&MemoryUseFact> {
    let uses = memory.uses_by_inst.get(&inst)?;
    let [use_fact] = uses.as_slice() else {
        return None;
    };
    Some(use_fact)
}

fn exact_def(memory: &MemorySSAFacts, inst: InstId) -> Option<&MemoryDefFact> {
    let defs = memory.defs_by_inst.get(&inst)?;
    let [def] = defs.as_slice() else {
        return None;
    };
    Some(def)
}

fn statement_matches_region(
    artifact: &SsaArtifact,
    statement: &CertifiedMemoryStatement,
    object: ObjectId,
    range: CertifiedNormalizedStackRange,
    ledger: &ObligationLedger,
    structured: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
) -> bool {
    let Some(width_bytes) = statement.width_bits().checked_div(8) else {
        return false;
    };
    let Some(access) = structured.get(&statement.access()) else {
        return false;
    };
    statement.validate(artifact.obligations()).is_ok()
        && super::try_certified_memory_statement(artifact, statement.access().inst)
            .ok()
            .flatten()
            .as_ref()
            == Some(statement)
        && frame_statement_is_ledgered(statement, ledger)
        && statement.object() == object
        && statement.space() == MachineAddressSpace::Ram
        && statement.word_size_bytes() == 1
        && statement.width_bits() != 0
        && statement.width_bits() % 8 == 0
        && width_bytes == range.size_bytes()
        && access.id == statement.access()
        && access.id.ordinal == 0
        && access.object == object
        && access.space == r2il::SpaceId::Ram
        && access.address == statement.address().binding().value()
        && access.width == width_bytes
        && access.provenance_complete
        && artifact.graph().op_site_for_inst(access.id.inst)
            == Some((access.block_addr, access.op_index))
        && match statement.kind() {
            CertifiedMemoryStatementKind::Read { result } => {
                !access.is_write && access.value == Some(result.binding().value())
            }
            CertifiedMemoryStatementKind::Write { value } => {
                access.is_write && access.value == Some(value.binding().value())
            }
        }
}

fn exact_region_facts(
    artifact: &SsaArtifact,
    topology: &CertifiedSourceTopology,
    region: &CertifiedPrivateStackRegion,
    ledger: &ObligationLedger,
) -> Option<ExactRegionFacts> {
    exact_region_facts_from_retained(
        artifact,
        topology,
        region,
        ledger,
        &artifact.facts().memory,
        &artifact.facts().structured.memory_accesses,
    )
}

fn exact_region_facts_from_retained(
    artifact: &SsaArtifact,
    topology: &CertifiedSourceTopology,
    region: &CertifiedPrivateStackRegion,
    ledger: &ObligationLedger,
    memory_facts: &MemorySSAFacts,
    structured_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
) -> Option<ExactRegionFacts> {
    let [object] = region.objects() else {
        return None;
    };
    let object = *object;
    let range = region.accessed_range();
    if range.size_bytes() == 0
        || !matches!(
            artifact.objects().object(object).map(|object| &object.kind),
            Some(
                ObjectKind::StackSlot {
                    space: r2il::SpaceId::Ram,
                    ..
                } | ObjectKind::FrameObject {
                    space: r2il::SpaceId::Ram,
                    ..
                }
            )
        )
    {
        return None;
    }
    let memory = artifact.machine_context().memory_model();
    if !memory.is_available()
        || !memory.is_coherent()
        || memory
            .space(r2il::SpaceId::Ram)
            .is_none_or(|space| space.word_size_bytes() != 1)
    {
        return None;
    }
    let location = exact_location(object, range.size_bytes());
    let mut stores = BTreeMap::new();
    let mut loads = BTreeMap::new();
    let mut access_insts = BTreeSet::new();
    for access in region.accesses() {
        let statement = access.statement();
        if access.range() != range
            || !statement_matches_region(
                artifact,
                statement,
                object,
                range,
                ledger,
                structured_accesses,
            )
            || !access_insts.insert(statement.access().inst)
        {
            return None;
        }
        match statement.kind() {
            CertifiedMemoryStatementKind::Read { .. } => {
                let use_fact = exact_use(memory_facts, statement.access().inst)?;
                if use_fact.location != location
                    || use_fact.version.object != object
                    || use_fact.version.version == 0
                    || loads
                        .insert(
                            statement.access(),
                            CertifiedPrivateFrameLoad {
                                statement: statement.clone(),
                                version: use_fact.version,
                            },
                        )
                        .is_some()
                {
                    return None;
                }
            }
            CertifiedMemoryStatementKind::Write { .. } => {
                let def = exact_def(memory_facts, statement.access().inst)?;
                if def.location != location
                    || def.previous_version.object != object
                    || def.next_version.object != object
                    || def.next_version.version == 0
                    || stores
                        .insert(
                            statement.access().inst,
                            CertifiedPrivateFrameStore {
                                statement: statement.clone(),
                                previous_version: def.previous_version,
                                next_version: def.next_version,
                            },
                        )
                        .is_some()
                {
                    return None;
                }
            }
        }
    }
    if region.accesses().is_empty() {
        return None;
    }

    // The region manifest and MemorySSA must describe the same complete set of
    // accesses for this object; partial or alternate-location facts are refused.
    let all_use_insts = memory_facts
        .uses_by_inst
        .iter()
        .flat_map(|(inst, facts)| facts.iter().map(move |fact| (*inst, fact)))
        .filter(|(_, fact)| fact.location.object == object || fact.version.object == object)
        .collect::<Vec<_>>();
    let all_def_insts = memory_facts
        .defs_by_inst
        .iter()
        .flat_map(|(inst, facts)| facts.iter().map(move |fact| (*inst, fact)))
        .filter(|(_, fact)| {
            fact.location.object == object
                || fact.previous_version.object == object
                || fact.next_version.object == object
        })
        .collect::<Vec<_>>();
    if all_use_insts.len() != loads.len()
        || all_def_insts.len() != stores.len()
        || all_use_insts
            .iter()
            .any(|(inst, fact)| fact.location != location || !access_insts.contains(inst))
        || all_def_insts
            .iter()
            .any(|(inst, fact)| fact.location != location || !access_insts.contains(inst))
    {
        return None;
    }

    let mut phis = Vec::new();
    for (block_addr, facts) in &memory_facts.phis_by_block {
        for phi in facts.iter().filter(|phi| {
            phi.object == object
                || phi.location.object == object
                || phi.output_version.object == object
                || phi
                    .inputs
                    .iter()
                    .any(|(_, version)| version.object == object)
        }) {
            if phi.location != location
                || phi.object != object
                || phi.output_version.object != object
                || phi.output_version.version == 0
                || phi.inputs.len() < 2
                || phi
                    .inputs
                    .iter()
                    .any(|(_, version)| version.object != object || version.version == 0)
                || phi
                    .inputs
                    .iter()
                    .map(|(_, version)| *version)
                    .collect::<BTreeSet<_>>()
                    .len()
                    < 2
            {
                return None;
            }
            let expected = region_predecessors(artifact, topology, *block_addr)?;
            let actual = phi
                .inputs
                .iter()
                .map(|(predecessor, _)| *predecessor)
                .collect::<Vec<_>>();
            if actual != expected {
                return None;
            }
            phis.push(CertifiedPrivateFramePhi {
                block_addr: *block_addr,
                output_version: phi.output_version,
                inputs: phi
                    .inputs
                    .iter()
                    .map(|(predecessor, version)| CertifiedPrivateFramePhiInput {
                        predecessor: *predecessor,
                        version: *version,
                    })
                    .collect(),
            });
        }
    }
    let facts = ExactRegionFacts {
        object,
        range,
        stores,
        loads,
        phis,
    };
    exact_memory_state_replays(artifact, topology, &facts).then_some(facts)
}

fn region_predecessors(
    artifact: &SsaArtifact,
    topology: &CertifiedSourceTopology,
    block_addr: u64,
) -> Option<Vec<u64>> {
    let graph = artifact.graph();
    let block = graph.block(*graph.block_by_addr.get(&block_addr)?)?;
    let graph_predecessors = block
        .predecessors
        .iter()
        .map(|predecessor| graph.block(*predecessor).map(|block| block.addr))
        .collect::<Option<Vec<_>>>()?;
    let source_predecessors = topology.block(block_addr)?.predecessors();
    (graph_predecessors.as_slice() == source_predecessors).then(|| source_predecessors.to_vec())
}

fn definition_dominates_block(
    artifact: &SsaArtifact,
    definition: &CertifiedPrivateFrameVersionDefinition,
    block_addr: u64,
) -> bool {
    let definition_block = match definition {
        CertifiedPrivateFrameVersionDefinition::Store(store) => artifact
            .graph()
            .inst(store.statement().access().inst)
            .and_then(|inst| artifact.graph().block(inst.block))
            .map(|block| block.addr),
        CertifiedPrivateFrameVersionDefinition::Phi(phi) => Some(phi.block_addr()),
    };
    definition_block
        .is_some_and(|definition_block| artifact.function().dominates(definition_block, block_addr))
}

fn definition_dominates_load(
    artifact: &SsaArtifact,
    definition: &CertifiedPrivateFrameVersionDefinition,
    load: &CertifiedPrivateFrameLoad,
) -> bool {
    match definition {
        CertifiedPrivateFrameVersionDefinition::Store(store) => frame_instruction_dominates(
            artifact,
            store.statement().access().inst,
            load.statement().access().inst,
        ),
        CertifiedPrivateFrameVersionDefinition::Phi(phi) => artifact
            .graph()
            .inst(load.statement().access().inst)
            .and_then(|inst| artifact.graph().block(inst.block))
            .is_some_and(|block| artifact.function().dominates(phi.block_addr(), block.addr)),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VisitState {
    Visiting,
    Visited,
}

fn visit_version(
    artifact: &SsaArtifact,
    version: MemoryVersion,
    definitions: &BTreeMap<MemoryVersion, CertifiedPrivateFrameVersionDefinition>,
    states: &mut BTreeMap<MemoryVersion, VisitState>,
    visited: &mut BTreeSet<MemoryVersion>,
) -> bool {
    if version.version == 0 {
        return false;
    }
    match states.get(&version) {
        Some(VisitState::Visiting) => return false,
        Some(VisitState::Visited) => return true,
        None => {}
    }
    let Some(definition) = definitions.get(&version) else {
        return false;
    };
    states.insert(version, VisitState::Visiting);
    if let CertifiedPrivateFrameVersionDefinition::Phi(phi) = definition {
        for input in phi.inputs() {
            let Some(child) = definitions.get(&input.version()) else {
                return false;
            };
            if !definition_dominates_block(artifact, child, input.predecessor())
                || !visit_version(artifact, input.version(), definitions, states, visited)
            {
                return false;
            }
        }
    }
    states.insert(version, VisitState::Visited);
    visited.insert(version);
    true
}

fn flow_for_load(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    region: &CertifiedPrivateStackRegion,
    facts: &ExactRegionFacts,
    load: &CertifiedPrivateFrameLoad,
) -> Option<CertifiedPrivateFrameValueFlow> {
    if !exact_memory_state_replays(artifact, origin.topology(), facts)
        || facts.loads.get(&load.statement().access()) != Some(load)
    {
        return None;
    }
    let mut definitions = BTreeMap::new();
    for store in facts.stores.values() {
        if definitions
            .insert(
                store.next_version(),
                CertifiedPrivateFrameVersionDefinition::Store(store.clone()),
            )
            .is_some()
        {
            return None;
        }
    }
    for phi in &facts.phis {
        if definitions
            .insert(
                phi.output_version(),
                CertifiedPrivateFrameVersionDefinition::Phi(phi.clone()),
            )
            .is_some()
        {
            return None;
        }
    }
    let root = load.version();
    let root_definition = definitions.get(&root)?;
    if !definition_dominates_load(artifact, root_definition, load) {
        return None;
    }
    let mut states = BTreeMap::new();
    let mut visited = BTreeSet::new();
    if !visit_version(artifact, root, &definitions, &mut states, &mut visited) {
        return None;
    }
    let retained = visited
        .into_iter()
        .map(|version| definitions.get(&version).cloned())
        .collect::<Option<Vec<_>>>()?;
    Some(CertifiedPrivateFrameValueFlow {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        origin: origin.clone(),
        region: region.clone(),
        object: facts.object,
        range: facts.range,
        load: load.clone(),
        root_version: root,
        definitions: retained.into_boxed_slice(),
    })
}

pub(super) fn certified_private_frame_value_flows(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    stack: Option<&CertifiedStackDiscipline>,
    statements: &BTreeMap<r2ssa::CanonicalInstructionId, CertifiedMemoryStatement>,
    ledger: &ObligationLedger,
) -> BTreeMap<StructuredAccessId, CertifiedPrivateFrameValueFlow> {
    let Some(stack) = stack else {
        return BTreeMap::new();
    };
    if !private_frame_authority_is_exact(artifact, origin, stack, ledger) {
        return BTreeMap::new();
    }
    let stack_statements = stack
        .private_regions()
        .iter()
        .flat_map(|region| region.accesses())
        .map(|access| access.statement())
        .collect::<Vec<_>>();
    if stack_statements.iter().any(|statement| {
        statements.get(&statement.producer()) != Some(*statement)
            || !frame_statement_is_ledgered(statement, ledger)
    }) {
        return BTreeMap::new();
    }
    let mut flows = BTreeMap::new();
    for region in stack.private_regions() {
        let Some(facts) = exact_region_facts(artifact, origin.topology(), region, ledger) else {
            return BTreeMap::new();
        };
        for (access, load) in &facts.loads {
            let Some(flow) = flow_for_load(artifact, origin, region, &facts, load) else {
                return BTreeMap::new();
            };
            if flows.insert(*access, flow).is_some() {
                return BTreeMap::new();
            }
        }
    }
    flows
}

fn private_frame_authority_is_exact(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    stack: &CertifiedStackDiscipline,
    ledger: &ObligationLedger,
) -> bool {
    artifact_matches_origin(artifact, origin)
        && ledger.matches_origin(origin)
        && stack.schema_version() == CERTIFICATION_SCHEMA_VERSION
        && stack.origin() == origin
}

#[cfg(test)]
mod tests {
    use r2il::{AddressSpace, ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, MachineProjection, SemanticObligationKind,
        SourceFunctionInterface, SourceFunctionReturn, SourceStackAllocationContract,
        SourceStackGrowth,
    };

    use super::*;
    use crate::{
        CERTIFICATION_SCHEMA_VERSION, CertifiedArtifactOrigin, CertifiedAuthoritySeal,
        CertifiedExpr, CertifiedFunction, CertifiedMachineContext, FrameCertifiedParts,
        GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION, certified_expr_from_projection,
        certified_memory_statements, certified_return_controls, certified_source_topology,
        certified_stack_discipline,
    };

    fn frame_flow_artifact(with_join: bool, overwrite: bool) -> SsaArtifact {
        let sp = Varnode::register(0, 8);
        let ra = Varnode::register(8, 8);
        let mut blocks = Vec::new();
        let mut entry = R2ILBlock::new(0x4100, 4);
        entry.push(R2ILOp::IntSub {
            dst: sp.clone(),
            a: sp.clone(),
            b: Varnode::constant(16, 8),
        });
        if with_join {
            entry.push(R2ILOp::CBranch {
                target: Varnode::ram(0x4108, 8),
                cond: Varnode::constant(1, 1),
            });
            blocks.push(entry);
            for (address, value) in [(0x4104, 1), (0x4108, 0)] {
                // Both arms compute the same carrier. Retaining the same exact
                // unique storage makes the ordinary SSA join affine too; the
                // MemorySSA join under test remains independently versioned.
                let unique = 0x100;
                let slot = Varnode::unique(unique, 8);
                let mut arm = R2ILBlock::new(address, 4);
                arm.push(R2ILOp::IntAdd {
                    dst: slot.clone(),
                    a: sp.clone(),
                    b: Varnode::constant(8, 8),
                });
                arm.push(R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: slot.clone(),
                    val: Varnode::constant(value, 4),
                });
                if overwrite && address == 0x4104 {
                    arm.push(R2ILOp::Store {
                        space: SpaceId::Ram,
                        addr: slot,
                        val: Varnode::constant(2, 4),
                    });
                }
                arm.push(R2ILOp::Branch {
                    target: Varnode::ram(0x410c, 8),
                });
                blocks.push(arm);
            }
        } else {
            let slot = Varnode::unique(0x100, 8);
            entry.push(R2ILOp::IntAdd {
                dst: slot.clone(),
                a: sp.clone(),
                b: Varnode::constant(8, 8),
            });
            entry.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: slot.clone(),
                val: Varnode::constant(1, 4),
            });
            if overwrite {
                entry.push(R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: slot,
                    val: Varnode::constant(2, 4),
                });
            }
            blocks.push(entry);
        }
        let join_addr = if with_join { 0x410c } else { 0x4104 };
        let slot = Varnode::unique(0x110, 8);
        let released = Varnode::unique(0x118, 8);
        let mut join = R2ILBlock::new(join_addr, 4);
        join.push(R2ILOp::IntAdd {
            dst: slot.clone(),
            a: sp.clone(),
            b: Varnode::constant(8, 8),
        });
        join.push(R2ILOp::Load {
            dst: Varnode::unique(0x120, 4),
            space: SpaceId::Ram,
            addr: slot,
        });
        join.push(R2ILOp::IntAdd {
            dst: released.clone(),
            a: sp.clone(),
            b: Varnode::constant(16, 8),
        });
        join.push(R2ILOp::Copy {
            dst: sp.clone(),
            src: released,
        });
        join.push(R2ILOp::Return { target: ra });
        blocks.push(join);

        let mut arch = ArchSpec::new("private-frame-value-flow-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("sp", 0, 8));
        arch.add_register(RegisterDef::new("ra", 8, 8));
        arch.add_space(AddressSpace::ram(8));
        let storage = |offset| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = SourceFunctionInterface::new_exact(
            b"private-frame-value-flow-revision-1".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(8)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0)))
        .and_then(|interface| {
            interface.with_stack_allocation_contract(SourceStackAllocationContract::new(
                SourceStackGrowth::LowerAddresses,
            ))
        })
        .expect("exact private-frame interface");
        SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface)
            .expect("private-frame artifact")
    }

    struct FlowFixture {
        artifact: SsaArtifact,
        origin: CertifiedArtifactOrigin,
        ledger: ObligationLedger,
        stack: CertifiedStackDiscipline,
        statements: BTreeMap<r2ssa::CanonicalInstructionId, CertifiedMemoryStatement>,
    }

    fn flow_fixture(with_join: bool) -> FlowFixture {
        flow_fixture_shape(with_join, false)
    }

    fn flow_fixture_shape(with_join: bool, overwrite: bool) -> FlowFixture {
        let artifact = frame_flow_artifact(with_join, overwrite);
        let projection = MachineProjection::from_artifact(&artifact).expect("machine projection");
        let machine_context =
            CertifiedMachineContext::from_artifact(&artifact).expect("machine context");
        let topology = certified_source_topology(&artifact).expect("source topology");
        let statements = certified_memory_statements(&artifact).expect("memory statements");
        let returns = certified_return_controls(&artifact, &topology).expect("return controls");
        let mut expressions = BTreeMap::<r2ssa::CanonicalInstructionId, CertifiedExpr>::new();
        for entity in projection.entities() {
            let obligations = entity
                .source_obligations()
                .iter()
                .copied()
                .filter(|obligation| obligation.kind == SemanticObligationKind::LiveValueProducer)
                .collect::<BTreeSet<_>>();
            if !obligations.is_empty() {
                expressions.insert(
                    entity.producer(),
                    certified_expr_from_projection(&artifact, &projection, entity, obligations)
                        .expect("certified expression"),
                );
            }
        }
        let origin = CertifiedArtifactOrigin {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            lift_provenance_schema_version: GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION,
            lift_manifest_hash: 1,
            authority: CertifiedAuthoritySeal::new(),
            graph_snapshot: vec![1].into_boxed_slice(),
            prepare_mode: artifact.mode().into(),
            decompile_preparation: None,
            assumptions: artifact.facts().assumptions.clone(),
            machine_context,
            source: artifact.obligations().clone(),
            topology: topology.clone(),
        };
        let mut certification =
            CertifiedFunction::bound(origin.source().clone(), &origin).expect("bound ledger");
        for statement in statements.values() {
            for obligation in statement.source_obligations() {
                certification
                    .record_absorbed_statement(*obligation, statement.clone())
                    .expect("ledgered statement");
            }
        }
        for expression in expressions.values() {
            for obligation in expression.entity().source_obligations() {
                certification
                    .record_absorbed_expression(*obligation, expression.clone())
                    .expect("ledgered expression");
            }
        }
        for control in returns.values() {
            certification
                .record_absorbed_return(control.clone())
                .expect("ledgered return");
        }
        let ledger = certification.ledger().clone();
        let stack = certified_stack_discipline(
            &artifact,
            &origin,
            FrameCertifiedParts {
                projection: &projection,
                topology: &topology,
                expressions: &expressions,
                memory_statements: &statements,
                return_controls: &returns,
            },
            None,
            &ledger,
        )
        .expect("certified stack discipline");
        FlowFixture {
            artifact,
            origin,
            ledger,
            stack,
            statements,
        }
    }

    fn single_region_facts(fixture: &FlowFixture) -> ExactRegionFacts {
        let [region] = fixture.stack.private_regions() else {
            panic!("one exact private region");
        };
        exact_region_facts(
            &fixture.artifact,
            fixture.origin.topology(),
            region,
            &fixture.ledger,
        )
        .expect("exact private region facts")
    }

    #[test]
    fn certifies_exact_direct_store_to_load_flow() {
        let fixture = flow_fixture(false);
        let facts = single_region_facts(&fixture);
        assert_eq!(facts.loads.len(), 1);
        let load = facts.loads.values().next().expect("one private load");
        let region = &fixture.stack.private_regions()[0];
        let flow = flow_for_load(&fixture.artifact, &fixture.origin, region, &facts, load)
            .expect("direct private-frame flow");
        assert_eq!(flow.schema_version(), CERTIFICATION_SCHEMA_VERSION);
        assert_eq!(flow.root_version(), load.version());
        assert_eq!(flow.definitions().len(), 1);
        let store = flow.definitions()[0].store().expect("store leaf");
        assert_eq!(store.previous_version().version, 0);
        assert_eq!(store.next_version(), flow.root_version());
        assert_eq!(
            flow.definition(flow.root_version()),
            Some(&flow.definitions()[0])
        );
    }

    #[test]
    fn certifies_two_store_memory_phi_to_load_flow_in_exact_predecessor_order() {
        let fixture = flow_fixture(true);
        let facts = single_region_facts(&fixture);
        assert_eq!(facts.loads.len(), 1);
        let load = facts.loads.values().next().expect("one joined load");
        let flow = flow_for_load(
            &fixture.artifact,
            &fixture.origin,
            &fixture.stack.private_regions()[0],
            &facts,
            load,
        )
        .expect("joined private-frame flow");
        assert_eq!(flow.definitions().len(), 3);
        let root = flow
            .definition(flow.root_version())
            .and_then(CertifiedPrivateFrameVersionDefinition::phi)
            .expect("root MemorySSA phi");
        assert_eq!(root.block_addr(), 0x410c);
        assert_eq!(
            root.inputs()
                .iter()
                .map(CertifiedPrivateFramePhiInput::predecessor)
                .collect::<Vec<_>>(),
            fixture
                .origin
                .topology()
                .block(0x410c)
                .expect("join topology")
                .predecessors()
        );
        assert_eq!(
            root.inputs()
                .iter()
                .map(CertifiedPrivateFramePhiInput::version)
                .collect::<BTreeSet<_>>()
                .len(),
            2
        );
        assert!(root.inputs().iter().all(|input| {
            flow.definition(input.version())
                .and_then(CertifiedPrivateFrameVersionDefinition::store)
                .is_some()
        }));
    }

    #[test]
    fn refuses_zero_missing_cyclic_and_colliding_version_paths() {
        let fixture = flow_fixture(true);
        let mut facts = single_region_facts(&fixture);
        let load = facts.loads.values().next().expect("joined load").clone();
        let region = &fixture.stack.private_regions()[0];

        let mut zero = load.clone();
        zero.version.version = 0;
        assert!(flow_for_load(&fixture.artifact, &fixture.origin, region, &facts, &zero).is_none());

        let removed = facts.stores.pop_first().expect("store definition");
        assert!(flow_for_load(&fixture.artifact, &fixture.origin, region, &facts, &load).is_none());
        facts.stores.insert(removed.0, removed.1);

        let phi_output = facts.phis[0].output_version;
        facts.phis[0].inputs[0].version = phi_output;
        assert!(flow_for_load(&fixture.artifact, &fixture.origin, region, &facts, &load).is_none());
        facts = single_region_facts(&fixture);

        facts.phis[0].output_version = facts.stores.values().next().unwrap().next_version();
        assert!(flow_for_load(&fixture.artifact, &fixture.origin, region, &facts, &load).is_none());

        facts = single_region_facts(&fixture);
        let store_version = facts.stores.values().next().unwrap().next_version();
        facts.loads.values_mut().next().unwrap().version = store_version;
        let nondominating = facts.loads.values().next().unwrap().clone();
        assert!(
            flow_for_load(
                &fixture.artifact,
                &fixture.origin,
                region,
                &facts,
                &nondominating,
            )
            .is_none()
        );

        facts = single_region_facts(&fixture);
        let original_output = facts.phis[0].output_version;
        let second_output = MemoryVersion {
            object: facts.object,
            version: 99,
        };
        let mut second = facts.phis[0].clone();
        second.output_version = second_output;
        second.inputs[0].version = original_output;
        facts.phis[0].inputs[0].version = second_output;
        facts.phis.push(second);
        assert!(flow_for_load(&fixture.artifact, &fixture.origin, region, &facts, &load).is_none());
    }

    #[test]
    fn refuses_dominating_but_non_reaching_store_versions() {
        let fixture = flow_fixture_shape(false, true);
        let mut facts = single_region_facts(&fixture);
        let region = &fixture.stack.private_regions()[0];
        let load = facts
            .loads
            .values()
            .next()
            .expect("overwritten load")
            .clone();
        let stores = facts.stores.values().cloned().collect::<Vec<_>>();
        let [earlier, later] = stores.as_slice() else {
            panic!("two ordered same-block stores");
        };
        assert_eq!(later.previous_version(), earlier.next_version());
        assert_eq!(load.version(), later.next_version());
        assert!(
            flow_for_load(&fixture.artifact, &fixture.origin, region, &facts, &load,).is_some()
        );

        let mut stale_load = load.clone();
        stale_load.version = earlier.next_version();
        facts
            .loads
            .insert(stale_load.statement().access(), stale_load.clone());
        assert!(
            flow_for_load(
                &fixture.artifact,
                &fixture.origin,
                region,
                &facts,
                &stale_load,
            )
            .is_none()
        );

        facts = single_region_facts(&fixture);
        let later_inst = *facts.stores.keys().next_back().expect("later store");
        facts.stores.get_mut(&later_inst).unwrap().previous_version = MemoryVersion {
            object: facts.object,
            version: 0,
        };
        let load = facts.loads.values().next().unwrap().clone();
        assert!(
            flow_for_load(&fixture.artifact, &fixture.origin, region, &facts, &load,).is_none()
        );

        let fixture = flow_fixture_shape(true, true);
        let mut facts = single_region_facts(&fixture);
        let region = &fixture.stack.private_regions()[0];
        let predecessor = 0x4104;
        let arm_stores = facts
            .stores
            .values()
            .filter(|store| {
                fixture
                    .artifact
                    .graph()
                    .inst(store.statement().access().inst)
                    .and_then(|inst| fixture.artifact.graph().block(inst.block))
                    .is_some_and(|block| block.addr == predecessor)
            })
            .cloned()
            .collect::<Vec<_>>();
        let [earlier, later] = arm_stores.as_slice() else {
            panic!("two predecessor stores");
        };
        let input = facts.phis[0]
            .inputs
            .iter_mut()
            .find(|input| input.predecessor == predecessor)
            .expect("predecessor phi input");
        assert_eq!(input.version, later.next_version());
        input.version = earlier.next_version();
        let load = facts.loads.values().next().unwrap().clone();
        assert!(
            flow_for_load(&fixture.artifact, &fixture.origin, region, &facts, &load,).is_none()
        );
    }

    #[test]
    fn refuses_duplicate_and_mutated_retained_access_facts() {
        let fixture = flow_fixture(false);
        let region = fixture.stack.private_regions()[0].clone();
        let base_memory = fixture.artifact.facts().memory.clone();
        let base_structured = fixture.artifact.facts().structured.memory_accesses.clone();
        let refuses = |memory: &MemorySSAFacts,
                       structured: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
                       region: &CertifiedPrivateStackRegion| {
            exact_region_facts_from_retained(
                &fixture.artifact,
                fixture.origin.topology(),
                region,
                &fixture.ledger,
                memory,
                structured,
            )
            .is_none()
        };

        let mut memory = base_memory.clone();
        let uses = memory.uses_by_inst.values_mut().next().expect("load use");
        uses.push(uses[0].clone());
        assert!(refuses(&memory, &base_structured, &region));

        let mut memory = base_memory.clone();
        let defs = memory.defs_by_inst.values_mut().next().expect("store def");
        defs.push(defs[0].clone());
        assert!(refuses(&memory, &base_structured, &region));

        let private_object = region.objects()[0];
        let other_object = ObjectId(private_object.0 + 99);
        let mut memory = base_memory.clone();
        let mut hidden_use = memory
            .uses_by_inst
            .values()
            .next()
            .and_then(|facts| facts.first())
            .expect("load use")
            .clone();
        hidden_use.location.object = other_object;
        assert_eq!(hidden_use.version.object, private_object);
        memory
            .uses_by_inst
            .insert(InstId(u32::MAX), vec![hidden_use]);
        assert!(refuses(&memory, &base_structured, &region));

        for keep_private_next in [false, true] {
            let mut memory = base_memory.clone();
            let mut hidden_def = memory
                .defs_by_inst
                .values()
                .next()
                .and_then(|facts| facts.first())
                .expect("store def")
                .clone();
            hidden_def.location.object = other_object;
            if keep_private_next {
                hidden_def.previous_version.object = other_object;
                assert_eq!(hidden_def.next_version.object, private_object);
            } else {
                hidden_def.next_version.object = other_object;
                assert_eq!(hidden_def.previous_version.object, private_object);
            }
            memory
                .defs_by_inst
                .insert(InstId(u32::MAX), vec![hidden_def]);
            assert!(refuses(&memory, &base_structured, &region));
        }

        for mutation in 0..4 {
            let mut memory = base_memory.clone();
            let location = &mut memory.uses_by_inst.values_mut().next().unwrap()[0].location;
            match mutation {
                0 => location.space = SpaceId::Custom(7),
                1 => location.address = RelativeMemoryAddress::Exact(1),
                2 => location.object = ObjectId(location.object.0 + 99),
                3 => location.size += 1,
                _ => unreachable!(),
            }
            assert!(refuses(&memory, &base_structured, &region));
        }

        for mutation in 0..4 {
            let mut structured = base_structured.clone();
            let access = structured.values_mut().next().expect("structured access");
            match mutation {
                0 => access.space = SpaceId::Custom(7),
                1 => access.object = ObjectId(access.object.0 + 99),
                2 => access.width += 1,
                3 => access.address = r2ssa::ValueId(access.address.0 + 99),
                _ => unreachable!(),
            }
            assert!(refuses(&base_memory, &structured, &region));
        }

        let mut wrong_range = region.clone();
        wrong_range.accessed_range.size_bytes += 1;
        assert!(refuses(&base_memory, &base_structured, &wrong_range));

        let mut wrong_access_range = region.clone();
        wrong_access_range.accesses[0].range.offset += 1;
        assert!(refuses(&base_memory, &base_structured, &wrong_access_range));
    }

    #[test]
    fn refuses_mutated_memory_phi_identity_and_topology() {
        let fixture = flow_fixture(true);
        let region = fixture.stack.private_regions()[0].clone();
        let base_memory = fixture.artifact.facts().memory.clone();
        let structured = &fixture.artifact.facts().structured.memory_accesses;
        let refuses = |memory: &MemorySSAFacts| {
            exact_region_facts_from_retained(
                &fixture.artifact,
                fixture.origin.topology(),
                &region,
                &fixture.ledger,
                memory,
                structured,
            )
            .is_none()
        };
        let mutate_phi = |label: &str, mutator: &dyn Fn(&mut r2ssa::MemoryPhiFact)| {
            let mut memory = base_memory.clone();
            let phi = memory
                .phis_by_block
                .values_mut()
                .next()
                .and_then(|phis| phis.first_mut())
                .expect("MemorySSA phi");
            mutator(phi);
            assert!(refuses(&memory), "phi mutation must refuse: {label}");
        };

        mutate_phi("zero input", &|phi| phi.inputs[0].1.version = 0);
        mutate_phi("identical inputs", &|phi| phi.inputs[1].1 = phi.inputs[0].1);
        mutate_phi("missing predecessor", &|phi| {
            phi.inputs.pop();
        });
        mutate_phi("duplicate predecessor", &|phi| {
            phi.inputs[1].0 = phi.inputs[0].0
        });
        mutate_phi("reordered predecessor", &|phi| phi.inputs.swap(0, 1));
        mutate_phi("location space", &|phi| {
            phi.location.space = SpaceId::Custom(7)
        });
        mutate_phi("location address", &|phi| {
            phi.location.address = RelativeMemoryAddress::Exact(1)
        });
        mutate_phi("location width", &|phi| phi.location.size += 1);
        mutate_phi("phi object", &|phi| {
            phi.object = ObjectId(phi.object.0 + 99)
        });
        mutate_phi("output object", &|phi| {
            phi.output_version.object = ObjectId(phi.object.0 + 99)
        });
        mutate_phi("zero output", &|phi| phi.output_version.version = 0);
    }

    #[test]
    fn refuses_foreign_ledger_origin_stack_and_missing_statement_authority() {
        let fixture = flow_fixture(false);
        let foreign = flow_fixture(false);
        assert_ne!(fixture.origin, foreign.origin);
        assert_ne!(fixture.stack.origin(), &foreign.origin);
        assert!(!fixture.ledger.matches_origin(&foreign.origin));
        assert!(!foreign.ledger.matches_origin(&fixture.origin));
        assert!(!private_frame_authority_is_exact(
            &fixture.artifact,
            &fixture.origin,
            &fixture.stack,
            &foreign.ledger,
        ));
        assert!(!private_frame_authority_is_exact(
            &fixture.artifact,
            &foreign.origin,
            &fixture.stack,
            &fixture.ledger,
        ));
        assert!(!private_frame_authority_is_exact(
            &fixture.artifact,
            &fixture.origin,
            &foreign.stack,
            &fixture.ledger,
        ));

        let mut statements = fixture.statements.clone();
        statements.clear();
        let stack_statement = fixture.stack.private_regions()[0].accesses()[0].statement();
        assert_ne!(
            statements.get(&stack_statement.producer()),
            Some(stack_statement)
        );
    }
}
