//! Opaque ownership for one coherent source-function snapshot.
//!
//! This crate is the source-side trust owner between radare2 and the lifting,
//! SSA, and certification layers.  It intentionally exposes no constructor
//! that accepts detached blocks, layouts, interfaces, hashes, or revision
//! identifiers.  A later `radare-v2` ingestion module is the only place that
//! may deep-copy the opaque radare snapshot into [`OwnedFunctionSnapshot`].
//! Stable hashes remain diagnostics; exact authority is the retained `Arc`
//! identity of one capture event.

use std::collections::BTreeSet;
use std::sync::Arc;

mod contracts;
mod radare_abi138;

pub use contracts::*;
pub use radare_abi138::*;

/// Endianness captured from the active analyzer configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SourceEndianness {
    Little,
    Big,
}

/// Exact analyzer tuple used later to select one embedded trusted Sleigh
/// profile.  Matching is exact; aliases, wildcards, and host fallbacks are not
/// part of this type's contract.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MachineProfile {
    arch_id: Box<str>,
    cpu_id: Box<str>,
    bits: u32,
    endianness: SourceEndianness,
}

impl MachineProfile {
    pub fn arch_id(&self) -> &str {
        &self.arch_id
    }

    pub fn cpu_id(&self) -> &str {
        &self.cpu_id
    }

    pub const fn bits(&self) -> u32 {
        self.bits
    }

    pub const fn endianness(&self) -> SourceEndianness {
        self.endianness
    }
}

/// Immutable identity fields copied from one source transaction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FunctionIdentity {
    address: u64,
}

impl FunctionIdentity {
    pub const fn address(&self) -> u64 {
        self.address
    }
}

/// Non-semantic presentation copied from the source owner.  It is deliberately
/// separate from [`FunctionIdentity`] so names cannot participate in semantic
/// equality, hashing, routing, or cache identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionPresentation {
    display_name: Box<str>,
    parameter_names: Box<[Box<str>]>,
}

impl FunctionPresentation {
    pub fn display_name(&self) -> &str {
        &self.display_name
    }

    pub fn parameter_names(&self) -> &[Box<str>] {
        &self.parameter_names
    }
}

/// Advisory CFG edge kind supplied by radare2.
///
/// These edges never grant machine authority.  The trusted Sleigh lift must
/// independently derive control flow and require an exact bijection before a
/// function can become certifiable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AdvisorySuccessorKind {
    Direct,
    Fallthrough,
    SwitchCase,
    SwitchDefault,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AdvisorySuccessor {
    kind: AdvisorySuccessorKind,
    target: u64,
    case_value: Option<u64>,
    external: bool,
}

impl AdvisorySuccessor {
    pub const fn kind(&self) -> AdvisorySuccessorKind {
        self.kind
    }

    pub const fn target(&self) -> u64 {
        self.target
    }

    pub const fn case_value(&self) -> Option<u64> {
        self.case_value
    }

    pub const fn is_external(&self) -> bool {
        self.external
    }
}

/// Exact owned bytes for one source-declared basic-block extent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedFunctionBlock {
    address: u64,
    bytes: Arc<[u8]>,
    successors: Box<[AdvisorySuccessor]>,
    switch_instruction: Option<u64>,
}

impl OwnedFunctionBlock {
    pub const fn address(&self) -> u64 {
        self.address
    }

    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub const fn successors(&self) -> &[AdvisorySuccessor] {
        &self.successors
    }

    pub const fn switch_instruction(&self) -> Option<u64> {
        self.switch_instruction
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedFunctionImage {
    entry_address: u64,
    blocks: Box<[OwnedFunctionBlock]>,
    external_exits: Box<[u64]>,
    total_source_bytes: usize,
}

impl OwnedFunctionImage {
    pub const fn entry_address(&self) -> u64 {
        self.entry_address
    }

    pub const fn blocks(&self) -> &[OwnedFunctionBlock] {
        &self.blocks
    }

    pub const fn external_exits(&self) -> &[u64] {
        &self.external_exits
    }

    pub const fn total_source_bytes(&self) -> usize {
        self.total_source_bytes
    }

    /// Structural ingress contract applied before an owned snapshot exists.
    /// Advisory edges are checked for internal consistency here; trusted lift
    /// code must still independently derive and exactly compare machine CFG.
    #[allow(dead_code)]
    fn is_structurally_valid(&self) -> bool {
        if self.blocks.is_empty()
            || !self
                .blocks
                .iter()
                .any(|block| block.address == self.entry_address)
        {
            return false;
        }
        let mut previous_end = None;
        let mut starts = BTreeSet::new();
        let mut byte_sum = 0usize;
        for block in &self.blocks {
            if block.bytes.is_empty() || !starts.insert(block.address) {
                return false;
            }
            let Ok(size) = u64::try_from(block.bytes.len()) else {
                return false;
            };
            let Some(end) = block.address.checked_add(size) else {
                return false;
            };
            if previous_end.is_some_and(|previous| block.address < previous) {
                return false;
            }
            let Some(next_sum) = byte_sum.checked_add(block.bytes.len()) else {
                return false;
            };
            byte_sum = next_sum;
            if block
                .switch_instruction
                .is_some_and(|address| address < block.address || address >= end)
            {
                return false;
            }
            previous_end = Some(end);
        }
        if byte_sum != self.total_source_bytes {
            return false;
        }
        let mut observed_external = BTreeSet::new();
        for block in &self.blocks {
            let mut unique = BTreeSet::new();
            let has_switch = block.switch_instruction.is_some();
            let mut switch_case_count = 0usize;
            let mut switch_default_count = 0usize;
            for successor in &block.successors {
                if !unique.insert((successor.kind, successor.target, successor.case_value)) {
                    return false;
                }
                let is_switch = matches!(
                    successor.kind,
                    AdvisorySuccessorKind::SwitchCase | AdvisorySuccessorKind::SwitchDefault
                );
                if is_switch && !has_switch
                    || matches!(successor.kind, AdvisorySuccessorKind::SwitchCase)
                        != successor.case_value.is_some()
                {
                    return false;
                }
                match successor.kind {
                    AdvisorySuccessorKind::SwitchCase => switch_case_count += 1,
                    AdvisorySuccessorKind::SwitchDefault => switch_default_count += 1,
                    AdvisorySuccessorKind::Direct | AdvisorySuccessorKind::Fallthrough => {}
                }
                let internal = starts.contains(&successor.target);
                let interior = self.blocks.iter().any(|candidate| {
                    u64::try_from(candidate.bytes.len())
                        .ok()
                        .and_then(|size| candidate.address.checked_add(size))
                        .is_some_and(|end| {
                            candidate.address < successor.target && successor.target < end
                        })
                });
                if interior || successor.external == internal {
                    return false;
                }
                if successor.external {
                    observed_external.insert(successor.target);
                }
            }
            // A dispatch block must name at least one case. Its default is
            // optional, because a switch whose input is proven in range has no
            // default edge, and the source describes exactly the edges that
            // exist rather than requiring a synthetic one. A dispatch block may
            // additionally carry the linear flow edge, so non-switch successors
            // are not evidence of an inconsistent block.
            if has_switch && (switch_case_count == 0 || switch_default_count > 1) {
                return false;
            }
        }
        self.external_exits.iter().copied().collect::<BTreeSet<_>>() == observed_external
            && self.external_exits.windows(2).all(|pair| pair[0] < pair[1])
    }
}

/// Advisory call metadata copied from the source snapshot. This projection
/// does not claim exact call-site identity, so it cannot create a call
/// certificate. It is retained only for diagnostics and future comparison
/// with machine-derived call identities.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdvisoryCallSite {
    instruction_address: u64,
    target_address: u64,
}

impl AdvisoryCallSite {
    pub const fn instruction_address(&self) -> u64 {
        self.instruction_address
    }

    pub const fn target_address(&self) -> u64 {
        self.target_address
    }
}

/// Closed vocabulary of source fields captured in the transaction.  The
/// future ABI adapter must reject unknown wire bits before constructing this
/// value.  Captured fields still do not independently authorize semantic
/// output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CapturedSourceFields {
    bounded_function_image: bool,
    function_interface: bool,
    exact_function_types: bool,
    exact_stack_slot_roles: bool,
    return_address_storage: bool,
    stack_pointer_storage: bool,
    frame_pointer_storage: bool,
    return_mechanism: bool,
    stack_allocation_contract: bool,
}

impl CapturedSourceFields {
    pub const fn has_bounded_function_image(self) -> bool {
        self.bounded_function_image
    }

    pub const fn has_function_interface(self) -> bool {
        self.function_interface
    }

    pub const fn has_exact_function_types(self) -> bool {
        self.exact_function_types
    }

    pub const fn has_exact_stack_slot_roles(self) -> bool {
        self.exact_stack_slot_roles
    }

    pub const fn has_return_address_storage(self) -> bool {
        self.return_address_storage
    }

    pub const fn has_stack_pointer_storage(self) -> bool {
        self.stack_pointer_storage
    }

    pub const fn has_frame_pointer_storage(self) -> bool {
        self.frame_pointer_storage
    }

    pub const fn has_return_mechanism(self) -> bool {
        self.return_mechanism
    }

    pub const fn has_stack_allocation_contract(self) -> bool {
        self.stack_allocation_contract
    }
}

/// Stable source payload identity retained for diagnostics and cache
/// partitioning only.  Equality of this value never substitutes for exact
/// capture lineage.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DiagnosticIdentity(u64);

impl DiagnosticIdentity {
    pub const fn value(self) -> u64 {
        self.0
    }
}

/// Fail-closed structural errors detected before capture authority exists.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SnapshotValidationError {
    InvalidMachineProfile,
    InvalidPresentation,
    EmptyRevisionIdentity,
    InvalidFunctionImage,
    InvalidAdvisoryCall,
    InvalidFunctionInterface,
}

impl std::fmt::Display for SnapshotValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid owned source snapshot: {self:?}")
    }
}

impl std::error::Error for SnapshotValidationError {}

#[derive(Debug)]
struct SnapshotState {
    machine: MachineProfile,
    function: FunctionIdentity,
    presentation: FunctionPresentation,
    image: OwnedFunctionImage,
    advisory_calls: Box<[AdvisoryCallSite]>,
    source_revision_identity: Box<[u8]>,
    function_interface: Option<SourceFunctionInterface>,
    machine_roles: SourceMachineRoles,
    captured_fields: CapturedSourceFields,
    diagnostics: DiagnosticIdentity,
}

/// One opaque, deeply owned, immutable source transaction.
///
/// There is deliberately no public constructor.  Clone retains the exact
/// capture event; independently captured identical bytes receive a different
/// identity.
#[derive(Clone)]
pub struct OwnedFunctionSnapshot(Arc<SnapshotState>);

impl OwnedFunctionSnapshot {
    /// The sole in-crate mint used by the future synchronous radare adapter.
    /// It is intentionally private: no external code can assemble source
    /// authority from detached pieces.
    #[allow(clippy::too_many_arguments, dead_code)]
    fn from_captured_parts(
        machine: MachineProfile,
        function: FunctionIdentity,
        presentation: FunctionPresentation,
        image: OwnedFunctionImage,
        advisory_calls: Box<[AdvisoryCallSite]>,
        source_revision_identity: Box<[u8]>,
        function_interface: Option<SourceFunctionInterface>,
        machine_roles: SourceMachineRoles,
        captured_fields: CapturedSourceFields,
        diagnostics: DiagnosticIdentity,
    ) -> Result<Self, SnapshotValidationError> {
        if machine.arch_id.is_empty()
            || machine.arch_id.contains('\0')
            || machine.cpu_id.is_empty()
            || machine.cpu_id.contains('\0')
            || !matches!(machine.bits, 32 | 64)
        {
            return Err(SnapshotValidationError::InvalidMachineProfile);
        }
        if presentation.display_name.contains('\0')
            || presentation
                .parameter_names
                .iter()
                .any(|name| name.contains('\0'))
            || function_interface.as_ref().is_some_and(|interface| {
                presentation.parameter_names.len() != interface.parameters().len()
            })
            || function_interface.is_none() && !presentation.parameter_names.is_empty()
        {
            return Err(SnapshotValidationError::InvalidPresentation);
        }
        if source_revision_identity.is_empty() {
            return Err(SnapshotValidationError::EmptyRevisionIdentity);
        }
        if function.address != image.entry_address
            || !captured_fields.bounded_function_image
            || !image.is_structurally_valid()
        {
            return Err(SnapshotValidationError::InvalidFunctionImage);
        }
        if captured_fields.function_interface != function_interface.is_some() {
            return Err(SnapshotValidationError::InvalidFunctionInterface);
        }
        // The machine carriers and an ABI that names the same carriers describe
        // one machine. If both are present they must agree, otherwise the two
        // views of the function contradict each other.
        if let Some(interface) = &function_interface
            && !machine_roles.is_empty()
        {
            if interface.return_address_storage().is_some()
                && interface.return_address_storage() != machine_roles.return_address_storage()
                || interface.stack_pointer_storage().is_some()
                    && interface.stack_pointer_storage() != machine_roles.stack_pointer_storage()
            {
                return Err(SnapshotValidationError::InvalidFunctionInterface);
            }
        }
        if let Some(interface) = &function_interface {
            if interface.revision_identity() != source_revision_identity.as_ref()
                || captured_fields.exact_function_types != interface.type_graph().is_some()
                || interface
                    .type_graph()
                    .is_some_and(|graph| !graph.validates_pointer_width(machine.bits))
                || captured_fields.exact_stack_slot_roles != interface.stack_slot_roles_complete()
                || captured_fields.return_address_storage
                    != interface.return_address_storage().is_some()
                || captured_fields.stack_pointer_storage
                    != interface.stack_pointer_storage().is_some()
                || captured_fields.frame_pointer_storage
                    != interface.frame_pointer_storage().is_some()
                || interface
                    .frame_pointer_storage()
                    .is_some_and(|storage| storage.size != machine.bits / 8)
                || captured_fields.return_mechanism != interface.return_mechanism().is_some()
                || captured_fields.stack_allocation_contract
                    != interface.stack_allocation_contract().is_some()
            {
                return Err(SnapshotValidationError::InvalidFunctionInterface);
            }
        } else if captured_fields.exact_function_types
            || captured_fields.exact_stack_slot_roles
            || captured_fields.return_address_storage
            || captured_fields.stack_pointer_storage
            || captured_fields.frame_pointer_storage
            || captured_fields.return_mechanism
            || captured_fields.stack_allocation_contract
        {
            return Err(SnapshotValidationError::InvalidFunctionInterface);
        }
        let mut identities = BTreeSet::new();
        for call in &advisory_calls {
            let inside_source = image.blocks.iter().any(|block| {
                u64::try_from(block.bytes.len())
                    .ok()
                    .and_then(|size| block.address.checked_add(size))
                    .is_some_and(|end| {
                        block.address <= call.instruction_address && call.instruction_address < end
                    })
            });
            if !inside_source || !identities.insert((call.instruction_address, call.target_address))
            {
                return Err(SnapshotValidationError::InvalidAdvisoryCall);
            }
        }
        Ok(Self(Arc::new(SnapshotState {
            machine,
            function,
            presentation,
            image,
            advisory_calls,
            source_revision_identity,
            function_interface,
            machine_roles,
            captured_fields,
            diagnostics,
        })))
    }

    pub fn machine(&self) -> &MachineProfile {
        &self.0.machine
    }

    pub fn function(&self) -> &FunctionIdentity {
        &self.0.function
    }

    pub fn presentation(&self) -> &FunctionPresentation {
        &self.0.presentation
    }

    pub fn image(&self) -> &OwnedFunctionImage {
        &self.0.image
    }

    pub fn advisory_calls(&self) -> &[AdvisoryCallSite] {
        &self.0.advisory_calls
    }

    pub fn source_revision_identity(&self) -> &[u8] {
        &self.0.source_revision_identity
    }

    pub fn function_interface(&self) -> Option<&SourceFunctionInterface> {
        self.0.function_interface.as_ref()
    }

    /// Borrow the machine carriers radare2 resolved from its register profile.
    ///
    /// These are present whether or not an ABI was recovered, so a function
    /// with no interface can still be reasoned about on its machine facts.
    pub fn machine_roles(&self) -> &SourceMachineRoles {
        &self.0.machine_roles
    }

    pub fn captured_fields(&self) -> CapturedSourceFields {
        self.0.captured_fields
    }

    pub fn diagnostic_identity(&self) -> DiagnosticIdentity {
        self.0.diagnostics
    }

    pub fn same_capture(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl std::fmt::Debug for OwnedFunctionSnapshot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OwnedFunctionSnapshot")
            .field("machine", self.machine())
            .field("function", self.function())
            .field("block_count", &self.image().blocks().len())
            .field("captured_fields", &self.captured_fields())
            .field("diagnostics", &self.diagnostic_identity())
            .finish_non_exhaustive()
    }
}

impl PartialEq for OwnedFunctionSnapshot {
    fn eq(&self, other: &Self) -> bool {
        self.same_capture(other)
    }
}

impl Eq for OwnedFunctionSnapshot {}

#[cfg(test)]
mod tests {
    use super::*;

    fn snapshot() -> OwnedFunctionSnapshot {
        OwnedFunctionSnapshot::from_captured_parts(
            MachineProfile {
                arch_id: "x86".into(),
                cpu_id: "x86-64".into(),
                bits: 64,
                endianness: SourceEndianness::Little,
            },
            FunctionIdentity { address: 0x1000 },
            FunctionPresentation {
                display_name: "fixture".into(),
                parameter_names: Box::new([]),
            },
            OwnedFunctionImage {
                entry_address: 0x1000,
                blocks: vec![OwnedFunctionBlock {
                    address: 0x1000,
                    bytes: Arc::from([0xc3]),
                    successors: Box::new([]),
                    switch_instruction: None,
                }]
                .into_boxed_slice(),
                external_exits: Box::new([]),
                total_source_bytes: 1,
            },
            Box::new([]),
            Box::from([7]),
            None,
            SourceMachineRoles::default(),
            CapturedSourceFields {
                bounded_function_image: true,
                function_interface: false,
                exact_function_types: false,
                exact_stack_slot_roles: false,
                return_address_storage: false,
                stack_pointer_storage: false,
                frame_pointer_storage: false,
                return_mechanism: false,
                stack_allocation_contract: false,
            },
            DiagnosticIdentity(7),
        )
        .expect("valid private capture")
    }

    fn register(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn exact_interface() -> SourceFunctionInterface {
        SourceFunctionInterface::new_exact(
            [7],
            "sysv",
            [SourceAbiParameterSpec::new(0, register(0))],
            SourceFunctionReturn::Register {
                storage: register(8),
            },
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(register(16)))
        .and_then(|interface| interface.with_stack_pointer_storage(register(24)))
        .and_then(|interface| interface.with_frame_pointer_storage(register(32)))
        .and_then(|interface| {
            interface.with_stack_allocation_contract(SourceStackAllocationContract::new(
                SourceStackGrowth::LowerAddresses,
            ))
        })
        .and_then(|interface| interface.with_exact_stacked_return(0, 8, 8, 8))
        .expect("exact interface")
    }

    #[test]
    fn clones_share_capture_but_reconstruction_does_not() {
        let first = snapshot();
        let clone = first.clone();
        let rebuilt = snapshot();
        assert!(first.same_capture(&clone));
        assert!(!first.same_capture(&rebuilt));
        assert_ne!(first, rebuilt);
        assert_eq!(first.image().blocks()[0].bytes(), [0xc3]);
        assert!(first.image().is_structurally_valid());
        assert_eq!(first.function().address(), 0x1000);
        assert_eq!(first.presentation().display_name(), "fixture");
    }

    #[test]
    fn structural_image_validation_rejects_unowned_or_incoherent_ranges() {
        let mut invalid = snapshot().image().clone();
        invalid.total_source_bytes = 2;
        assert!(!invalid.is_structurally_valid());

        let mut invalid = snapshot().image().clone();
        invalid.blocks[0].successors = vec![AdvisorySuccessor {
            kind: AdvisorySuccessorKind::Direct,
            target: 0x1000,
            case_value: None,
            external: true,
        }]
        .into_boxed_slice();
        assert!(!invalid.is_structurally_valid());
    }

    #[test]
    fn capture_rejects_function_identity_detached_from_image_entry() {
        let valid = snapshot();
        assert_eq!(
            OwnedFunctionSnapshot::from_captured_parts(
                valid.machine().clone(),
                FunctionIdentity { address: 0x2000 },
                valid.presentation().clone(),
                valid.image().clone(),
                valid.advisory_calls().to_vec().into_boxed_slice(),
                valid.source_revision_identity().into(),
                valid.function_interface().cloned(),
                *valid.machine_roles(),
                valid.captured_fields(),
                valid.diagnostic_identity(),
            ),
            Err(SnapshotValidationError::InvalidFunctionImage)
        );
    }

    #[test]
    fn capture_binds_interface_payload_and_capabilities_to_one_revision() {
        let valid = snapshot();
        let interface = exact_interface();
        let captured_fields = CapturedSourceFields {
            bounded_function_image: true,
            function_interface: true,
            exact_function_types: false,
            exact_stack_slot_roles: true,
            return_address_storage: true,
            stack_pointer_storage: true,
            frame_pointer_storage: true,
            return_mechanism: true,
            stack_allocation_contract: true,
        };
        let mut presentation = valid.presentation().clone();
        presentation.parameter_names = [Box::<str>::from("value")].into();
        let captured = OwnedFunctionSnapshot::from_captured_parts(
            valid.machine().clone(),
            *valid.function(),
            presentation,
            valid.image().clone(),
            Box::new([]),
            Box::from([7]),
            Some(interface.clone()),
            SourceMachineRoles::default(),
            captured_fields,
            valid.diagnostic_identity(),
        )
        .expect("coherent interface capture");
        assert_eq!(captured.function_interface(), Some(&interface));
        assert_eq!(
            captured.presentation().parameter_names()[0].as_ref(),
            "value"
        );
        assert!(captured.captured_fields().has_return_mechanism());
        assert!(captured.captured_fields().has_frame_pointer_storage());
        assert!(captured.captured_fields().has_stack_allocation_contract());
        let exact_presentation = captured.presentation().clone();

        let narrow = |offset| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 4,
        };
        let wrong_machine_width =
            SourceFunctionInterface::new_exact([7], "sysv", [], SourceFunctionReturn::Void, [])
                .and_then(|interface| interface.with_stack_pointer_storage(narrow(24)))
                .and_then(|interface| interface.with_frame_pointer_storage(narrow(32)))
                .expect("internally width-coherent narrow interface");
        let narrow_fields = CapturedSourceFields {
            bounded_function_image: true,
            function_interface: true,
            exact_function_types: false,
            exact_stack_slot_roles: true,
            return_address_storage: false,
            stack_pointer_storage: true,
            frame_pointer_storage: true,
            return_mechanism: false,
            stack_allocation_contract: false,
        };
        assert_eq!(
            OwnedFunctionSnapshot::from_captured_parts(
                valid.machine().clone(),
                *valid.function(),
                valid.presentation().clone(),
                valid.image().clone(),
                Box::new([]),
                Box::from([7]),
                Some(wrong_machine_width),
                SourceMachineRoles::default(),
                narrow_fields,
                valid.diagnostic_identity(),
            ),
            Err(SnapshotValidationError::InvalidFunctionInterface)
        );

        let mut missing_frame_pointer = captured_fields;
        missing_frame_pointer.frame_pointer_storage = false;
        assert_eq!(
            OwnedFunctionSnapshot::from_captured_parts(
                valid.machine().clone(),
                *valid.function(),
                exact_presentation.clone(),
                valid.image().clone(),
                Box::new([]),
                Box::from([7]),
                Some(interface.clone()),
                SourceMachineRoles::default(),
                missing_frame_pointer,
                valid.diagnostic_identity(),
            ),
            Err(SnapshotValidationError::InvalidFunctionInterface)
        );

        let mut missing_stack_allocation_contract = captured_fields;
        missing_stack_allocation_contract.stack_allocation_contract = false;
        assert_eq!(
            OwnedFunctionSnapshot::from_captured_parts(
                valid.machine().clone(),
                *valid.function(),
                exact_presentation.clone(),
                valid.image().clone(),
                Box::new([]),
                Box::from([7]),
                Some(interface.clone()),
                SourceMachineRoles::default(),
                missing_stack_allocation_contract,
                valid.diagnostic_identity(),
            ),
            Err(SnapshotValidationError::InvalidFunctionInterface)
        );

        let interface_without_frame_pointer = SourceFunctionInterface::new_exact(
            [7],
            "sysv",
            [SourceAbiParameterSpec::new(0, register(0))],
            SourceFunctionReturn::Register {
                storage: register(8),
            },
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                register(32),
                -8,
                8,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(register(16)))
        .and_then(|interface| interface.with_stack_pointer_storage(register(24)))
        .and_then(|interface| {
            interface.with_stack_allocation_contract(SourceStackAllocationContract::new(
                SourceStackGrowth::LowerAddresses,
            ))
        })
        .and_then(|interface| interface.with_exact_stacked_return(0, 8, 8, 8))
        .expect("interface without explicit frame fact");
        assert_eq!(
            interface_without_frame_pointer.exact_frame_pointer_storage(),
            Some(register(32))
        );
        assert_eq!(
            OwnedFunctionSnapshot::from_captured_parts(
                valid.machine().clone(),
                *valid.function(),
                exact_presentation.clone(),
                valid.image().clone(),
                Box::new([]),
                Box::from([7]),
                Some(interface_without_frame_pointer.clone()),
                SourceMachineRoles::default(),
                captured_fields,
                valid.diagnostic_identity(),
            ),
            Err(SnapshotValidationError::InvalidFunctionInterface)
        );
        let mut fields_without_frame_pointer = captured_fields;
        fields_without_frame_pointer.frame_pointer_storage = false;
        let captured_without_frame_pointer = OwnedFunctionSnapshot::from_captured_parts(
            valid.machine().clone(),
            *valid.function(),
            exact_presentation.clone(),
            valid.image().clone(),
            Box::new([]),
            Box::from([7]),
            Some(interface_without_frame_pointer),
            SourceMachineRoles::default(),
            fields_without_frame_pointer,
            valid.diagnostic_identity(),
        )
        .expect("absent frame bit means no explicit payload");
        assert_eq!(
            captured_without_frame_pointer
                .function_interface()
                .and_then(SourceFunctionInterface::frame_pointer_storage),
            None
        );

        let mut missing_return_mechanism = captured_fields;
        missing_return_mechanism.return_mechanism = false;
        assert_eq!(
            OwnedFunctionSnapshot::from_captured_parts(
                valid.machine().clone(),
                *valid.function(),
                exact_presentation.clone(),
                valid.image().clone(),
                Box::new([]),
                Box::from([7]),
                Some(interface.clone()),
                SourceMachineRoles::default(),
                missing_return_mechanism,
                valid.diagnostic_identity(),
            ),
            Err(SnapshotValidationError::InvalidFunctionInterface)
        );

        let mut mechanism_without_interface = valid.captured_fields();
        mechanism_without_interface.return_mechanism = true;
        assert_eq!(
            OwnedFunctionSnapshot::from_captured_parts(
                valid.machine().clone(),
                *valid.function(),
                valid.presentation().clone(),
                valid.image().clone(),
                Box::new([]),
                Box::from([7]),
                None,
                SourceMachineRoles::default(),
                mechanism_without_interface,
                valid.diagnostic_identity(),
            ),
            Err(SnapshotValidationError::InvalidFunctionInterface)
        );

        let mut frame_pointer_without_interface = valid.captured_fields();
        frame_pointer_without_interface.frame_pointer_storage = true;
        assert_eq!(
            OwnedFunctionSnapshot::from_captured_parts(
                valid.machine().clone(),
                *valid.function(),
                valid.presentation().clone(),
                valid.image().clone(),
                Box::new([]),
                Box::from([7]),
                None,
                SourceMachineRoles::default(),
                frame_pointer_without_interface,
                valid.diagnostic_identity(),
            ),
            Err(SnapshotValidationError::InvalidFunctionInterface)
        );

        let wrong_revision = SourceFunctionInterface::new_exact(
            [8],
            "sysv",
            [SourceAbiParameterSpec::new(0, register(0))],
            SourceFunctionReturn::Register {
                storage: register(8),
            },
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(register(16)))
        .and_then(|interface| interface.with_stack_pointer_storage(register(24)))
        .and_then(|interface| interface.with_exact_stacked_return(0, 8, 8, 8))
        .expect("structurally valid foreign interface");
        assert_eq!(
            OwnedFunctionSnapshot::from_captured_parts(
                valid.machine().clone(),
                *valid.function(),
                exact_presentation,
                valid.image().clone(),
                Box::new([]),
                Box::from([7]),
                Some(wrong_revision),
                SourceMachineRoles::default(),
                captured_fields,
                valid.diagnostic_identity(),
            ),
            Err(SnapshotValidationError::InvalidFunctionInterface)
        );
    }
}
