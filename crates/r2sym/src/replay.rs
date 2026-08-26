use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use r2il::ArchSpec;
use r2ssa::{CanonicalStorageId, CanonicalStorageSpace, SsaArtifact};

use crate::memory::MemoryRegionKind;
use crate::runtime::{seed_memory_regions_for_arch, seed_memory_regions_for_prepared};
use crate::state::SymState;

#[derive(Debug, Clone, Default)]
pub struct ReplaySeed {
    pub checkpoint_id: Option<u64>,
    pub entry_pc: Option<u64>,
    pub registers: Vec<ReplayRegisterValue>,
    pub memory: Vec<ReplayMemoryWindow>,
    pub register_overlays: Vec<ReplayRegisterOverlay>,
    pub memory_overlays: Vec<ReplayMemoryOverlay>,
    pub tty_fds: Vec<i32>,
    pub skip_sleep_calls: bool,
}

#[derive(Debug, Clone)]
pub struct ReplayRegisterValue {
    pub name: String,
    pub value: u64,
}

#[derive(Debug, Clone)]
pub struct ReplayMemoryWindow {
    pub addr: u64,
    pub bytes: Vec<u8>,
    pub label: Option<String>,
}

#[derive(Debug, Clone)]
pub struct ReplayRegisterOverlay {
    pub name: String,
    pub symbol: String,
}

#[derive(Debug, Clone)]
pub struct ReplayMemoryOverlay {
    pub addr: u64,
    pub size: u32,
    pub name: String,
}

/// Why a replay register snapshot could not be bound to one prepared machine.
///
/// Raw debugger/register names are input syntax only. The exact replay path
/// resolves them through the source-owned register map before selecting an SSA
/// entry value or a state presentation key. It never guesses aliases or widths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PreparedReplaySeedError {
    UnknownRegister(String),
    InvalidRegisterStorage {
        name: String,
        storage: CanonicalStorageId,
    },
    MissingEntryValue(CanonicalStorageId),
    AmbiguousEntryValue(CanonicalStorageId),
    ConflictingRegisterLocation {
        first: String,
        second: String,
    },
    RegisterWidthOverflow(CanonicalStorageId),
}

impl fmt::Display for PreparedReplaySeedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownRegister(name) => {
                write!(f, "replay register {name:?} has no source-owned storage")
            }
            Self::InvalidRegisterStorage { name, storage } => write!(
                f,
                "replay register {name:?} resolved to invalid storage {storage:?}"
            ),
            Self::MissingEntryValue(storage) => {
                write!(f, "replay storage {storage:?} has no SSA entry value")
            }
            Self::AmbiguousEntryValue(storage) => {
                write!(
                    f,
                    "replay storage {storage:?} has multiple SSA entry values"
                )
            }
            Self::ConflictingRegisterLocation { first, second } => write!(
                f,
                "replay registers {first:?} and {second:?} address one machine location"
            ),
            Self::RegisterWidthOverflow(storage) => {
                write!(f, "replay storage {storage:?} has an overflowing bit width")
            }
        }
    }
}

impl std::error::Error for PreparedReplaySeedError {}

#[derive(Debug)]
struct PreparedReplayRegisterValue<'a> {
    state_key: String,
    bits: u32,
    value: u64,
    _source_name: &'a str,
}

#[derive(Debug)]
struct PreparedReplayRegisterOverlay<'a> {
    state_key: String,
    bits: u32,
    symbol: &'a str,
    _source_name: &'a str,
}

#[derive(Debug)]
struct PreparedReplayRegisters<'a> {
    concrete: Vec<PreparedReplayRegisterValue<'a>>,
    symbolic: Vec<PreparedReplayRegisterOverlay<'a>>,
}

const REPLAY_FINGERPRINT_OFFSET_BASIS: u64 = 0xcbf29ce484222325;
const REPLAY_FINGERPRINT_PRIME: u64 = 0x100000001b3;

fn replay_fingerprint_update(state: &mut u64, bytes: &[u8]) {
    for byte in bytes {
        *state ^= u64::from(*byte);
        *state = state.wrapping_mul(REPLAY_FINGERPRINT_PRIME);
    }
}

fn replay_fingerprint_tag(state: &mut u64, tag: u8) {
    replay_fingerprint_update(state, &[tag]);
}

fn replay_fingerprint_u64(state: &mut u64, tag: u8, value: u64) {
    replay_fingerprint_tag(state, tag);
    replay_fingerprint_update(state, &value.to_le_bytes());
}

fn replay_fingerprint_bool(state: &mut u64, tag: u8, value: bool) {
    replay_fingerprint_tag(state, tag);
    replay_fingerprint_update(state, &[u8::from(value)]);
}

fn replay_fingerprint_str(state: &mut u64, tag: u8, value: &str) {
    replay_fingerprint_tag(state, tag);
    replay_fingerprint_update(state, &(value.len() as u64).to_le_bytes());
    replay_fingerprint_update(state, value.as_bytes());
}

fn replay_fingerprint_bytes(state: &mut u64, tag: u8, value: &[u8]) {
    replay_fingerprint_tag(state, tag);
    replay_fingerprint_update(state, &(value.len() as u64).to_le_bytes());
    replay_fingerprint_update(state, value);
}

fn canonical_replay_register_name(name: &str) -> String {
    name.trim().to_ascii_uppercase()
}

fn canonical_replay_label(label: &Option<String>) -> Option<&str> {
    label
        .as_deref()
        .map(str::trim)
        .filter(|label| !label.is_empty())
}

pub fn stable_replay_seed_fingerprint(seed: &ReplaySeed) -> u64 {
    let mut state = REPLAY_FINGERPRINT_OFFSET_BASIS;
    replay_fingerprint_tag(&mut state, 0x01);
    match seed.checkpoint_id {
        Some(value) => replay_fingerprint_u64(&mut state, 0x02, value),
        None => replay_fingerprint_tag(&mut state, 0x03),
    }
    match seed.entry_pc {
        Some(value) => replay_fingerprint_u64(&mut state, 0x04, value),
        None => replay_fingerprint_tag(&mut state, 0x05),
    }

    let mut registers: Vec<_> = seed
        .registers
        .iter()
        .map(|register| {
            (
                canonical_replay_register_name(&register.name),
                register.value,
            )
        })
        .collect();
    registers.sort_unstable();
    replay_fingerprint_u64(&mut state, 0x06, registers.len() as u64);
    for (name, value) in registers {
        replay_fingerprint_str(&mut state, 0x07, &name);
        replay_fingerprint_u64(&mut state, 0x08, value);
    }

    let mut memory: Vec<_> = seed
        .memory
        .iter()
        .map(|window| {
            (
                window.addr,
                canonical_replay_label(&window.label).map(str::to_string),
                window.bytes.clone(),
            )
        })
        .collect();
    memory.sort_unstable_by(|left, right| {
        left.0
            .cmp(&right.0)
            .then(left.1.cmp(&right.1))
            .then(left.2.cmp(&right.2))
    });
    replay_fingerprint_u64(&mut state, 0x09, memory.len() as u64);
    for (addr, label, bytes) in memory {
        replay_fingerprint_u64(&mut state, 0x0a, addr);
        match label {
            Some(label) => replay_fingerprint_str(&mut state, 0x0b, &label),
            None => replay_fingerprint_tag(&mut state, 0x0c),
        }
        replay_fingerprint_bytes(&mut state, 0x0d, &bytes);
    }

    let mut register_overlays: Vec<_> = seed
        .register_overlays
        .iter()
        .map(|overlay| {
            (
                canonical_replay_register_name(&overlay.name),
                overlay.symbol.trim().to_string(),
            )
        })
        .collect();
    register_overlays.sort_unstable();
    replay_fingerprint_u64(&mut state, 0x0e, register_overlays.len() as u64);
    for (name, symbol) in register_overlays {
        replay_fingerprint_str(&mut state, 0x0f, &name);
        replay_fingerprint_str(&mut state, 0x10, &symbol);
    }

    let mut memory_overlays: Vec<_> = seed
        .memory_overlays
        .iter()
        .map(|overlay| (overlay.addr, overlay.size, overlay.name.trim().to_string()))
        .collect();
    memory_overlays.sort_unstable();
    replay_fingerprint_u64(&mut state, 0x11, memory_overlays.len() as u64);
    for (addr, size, name) in memory_overlays {
        replay_fingerprint_u64(&mut state, 0x12, addr);
        replay_fingerprint_u64(&mut state, 0x13, u64::from(size));
        replay_fingerprint_str(&mut state, 0x14, &name);
    }

    let mut tty_fds = seed.tty_fds.clone();
    tty_fds.sort_unstable();
    replay_fingerprint_u64(&mut state, 0x15, tty_fds.len() as u64);
    for fd in tty_fds {
        replay_fingerprint_u64(&mut state, 0x16, fd as u64);
    }
    replay_fingerprint_bool(&mut state, 0x17, seed.skip_sleep_calls);
    state
}

fn exact_replay_state_key(
    prepared: &SsaArtifact,
    storage: CanonicalStorageId,
) -> Result<(String, u32), PreparedReplaySeedError> {
    let mut entry_values = prepared
        .graph()
        .values
        .iter()
        .filter(|value| value.canonical_storage == Some(storage))
        .filter(|value| prepared.graph().def_inst(value.id).is_none());
    let first = entry_values
        .next()
        .ok_or(PreparedReplaySeedError::MissingEntryValue(storage))?;
    if entry_values.next().is_some() {
        return Err(PreparedReplaySeedError::AmbiguousEntryValue(storage));
    }

    let bits = first
        .var
        .size
        .checked_mul(8)
        .ok_or(PreparedReplaySeedError::RegisterWidthOverflow(storage))?;
    if first.var.size != storage.size || bits == 0 {
        return Err(PreparedReplaySeedError::InvalidRegisterStorage {
            name: first.var.display_name(),
            storage,
        });
    }
    Ok((first.var.display_name(), bits))
}

fn bind_prepared_replay_registers<'a>(
    prepared: &SsaArtifact,
    seed: &'a ReplaySeed,
) -> Result<PreparedReplayRegisters<'a>, PreparedReplaySeedError> {
    let mut occupied_locations = BTreeMap::new();
    let mut exact_storages = BTreeSet::new();
    let mut concrete = Vec::with_capacity(seed.registers.len());
    let mut symbolic = Vec::with_capacity(seed.register_overlays.len());

    let mut bind = |name: &'a str| {
        let storage = prepared
            .machine_context()
            .register_storage(name)
            .ok_or_else(|| PreparedReplaySeedError::UnknownRegister(name.to_string()))?;
        if storage.space != CanonicalStorageSpace::Register || storage.size == 0 {
            return Err(PreparedReplaySeedError::InvalidRegisterStorage {
                name: name.to_string(),
                storage,
            });
        }
        if !exact_storages.insert(storage) {
            let first = occupied_locations
                .get(&storage.location())
                .cloned()
                .unwrap_or_else(|| name.to_string());
            return Err(PreparedReplaySeedError::ConflictingRegisterLocation {
                first,
                second: name.to_string(),
            });
        }
        if let Some(first) = occupied_locations.insert(storage.location(), name.to_string()) {
            return Err(PreparedReplaySeedError::ConflictingRegisterLocation {
                first,
                second: name.to_string(),
            });
        }
        let (state_key, bits) = exact_replay_state_key(prepared, storage)?;
        Ok((state_key, bits))
    };

    for register in &seed.registers {
        let (state_key, bits) = bind(&register.name)?;
        concrete.push(PreparedReplayRegisterValue {
            state_key,
            bits,
            value: register.value,
            _source_name: &register.name,
        });
    }
    for overlay in &seed.register_overlays {
        let (state_key, bits) = bind(&overlay.name)?;
        symbolic.push(PreparedReplayRegisterOverlay {
            state_key,
            bits,
            symbol: &overlay.symbol,
            _source_name: &overlay.name,
        });
    }

    Ok(PreparedReplayRegisters { concrete, symbolic })
}

/// Apply one replay seed through the exact source-owned machine/SSA contract.
///
/// Register bindings are validated as a whole before state is mutated. Unknown
/// names, overlapping aliases, ambiguous SSA entry values, and invalid widths
/// are typed refusals rather than architecture-derived guesses.
pub fn apply_replay_seed_to_prepared<'ctx>(
    state: &mut SymState<'ctx>,
    prepared: &SsaArtifact,
    seed: &ReplaySeed,
) -> Result<(), PreparedReplaySeedError> {
    let registers = bind_prepared_replay_registers(prepared, seed)?;
    apply_bound_prepared_replay(state, seed, registers);
    Ok(())
}

/// Seed canonical prepared memory regions, then apply an exact replay seed.
pub fn seed_replay_state_for_prepared<'ctx>(
    state: &mut SymState<'ctx>,
    prepared: &SsaArtifact,
    seed: &ReplaySeed,
) -> Result<(), PreparedReplaySeedError> {
    // Bind first so a rejected register contract leaves the state untouched.
    let registers = bind_prepared_replay_registers(prepared, seed)?;
    seed_memory_regions_for_prepared(state, prepared);
    apply_bound_prepared_replay(state, seed, registers);
    Ok(())
}

fn apply_bound_prepared_replay<'ctx>(
    state: &mut SymState<'ctx>,
    seed: &ReplaySeed,
    registers: PreparedReplayRegisters<'_>,
) {
    if let Some(entry_pc) = seed.entry_pc {
        state.set_static_execution_pc(entry_pc);
    }
    for register in registers.concrete {
        state.set_concrete(&register.state_key, register.value, register.bits);
    }
    apply_replay_memory_and_policy(state, seed);
    for overlay in registers.symbolic {
        state.make_symbolic_named(&overlay.state_key, overlay.symbol, overlay.bits);
    }
}

/// Apply replay input using advisory register names and architecture widths.
///
/// This compatibility API is for manual/unprepared callers only. Exact engine
/// requests must use [`seed_replay_state_for_prepared`] or
/// [`apply_replay_seed_to_prepared`].
pub fn seed_replay_state_for_arch<'ctx>(
    state: &mut SymState<'ctx>,
    prepared: Option<&SsaArtifact>,
    arch: Option<&ArchSpec>,
    seed: &ReplaySeed,
) {
    if let Some(prepared) = prepared {
        seed_memory_regions_for_arch(state, prepared, arch);
    }
    apply_replay_seed_to_state(state, prepared, arch, seed);
}

/// Legacy advisory/manual replay projection from register spellings.
///
/// Passing a prepared artifact here only improves presentation-name matching;
/// it does not make this API source-owned. Exact engine paths must use
/// [`apply_replay_seed_to_prepared`].
pub fn apply_replay_seed_to_state<'ctx>(
    state: &mut SymState<'ctx>,
    prepared: Option<&SsaArtifact>,
    arch: Option<&ArchSpec>,
    seed: &ReplaySeed,
) {
    if let Some(entry_pc) = seed.entry_pc {
        state.set_static_execution_pc(entry_pc);
    }

    let register_layout = ReplayRegisterLayout::from_prepared(prepared);
    for register in &seed.registers {
        let (seed_name, bits) = register_layout
            .resolve_register(&register.name)
            .unwrap_or_else(|| {
                (
                    register.name.to_ascii_uppercase(),
                    default_register_bits(arch),
                )
            });
        state.set_concrete(&seed_name, register.value, bits);
    }

    apply_replay_memory_and_policy(state, seed);

    for overlay in &seed.register_overlays {
        let (seed_name, bits) = register_layout
            .resolve_register(&overlay.name)
            .unwrap_or_else(|| {
                (
                    overlay.name.to_ascii_uppercase(),
                    default_register_bits(arch),
                )
            });
        state.make_symbolic_named(&seed_name, &overlay.symbol, bits);
    }
}

fn apply_replay_memory_and_policy<'ctx>(state: &mut SymState<'ctx>, seed: &ReplaySeed) {
    for (index, window) in seed.memory.iter().enumerate() {
        if window.bytes.is_empty() {
            continue;
        }
        let name = window
            .label
            .clone()
            .filter(|label| !label.is_empty())
            .unwrap_or_else(|| format!("replay_{index:x}_{:x}", window.addr));
        let region_id = state.define_memory_region(
            MemoryRegionKind::Replay,
            &name,
            Some(window.addr),
            Some(window.bytes.len() as u64),
        );
        state.seed_region_bytes(region_id, 0, &window.bytes);
    }

    for overlay in &seed.memory_overlays {
        if overlay.size == 0 {
            continue;
        }
        state.make_symbolic_memory(overlay.addr, overlay.size, &overlay.name);
    }

    for fd in &seed.tty_fds {
        state.set_tty_fd(*fd, true);
    }
    state.set_skip_sleep_calls(seed.skip_sleep_calls);
}

fn default_register_bits(arch: Option<&ArchSpec>) -> u32 {
    arch.map(|arch| arch.addr_size.max(1) * 8).unwrap_or(64)
}

#[derive(Default)]
struct ReplayRegisterLayout {
    by_name: BTreeMap<String, (String, u32)>,
    alias_candidates: BTreeMap<String, (u32, RegisterAliasSpec)>,
}

impl ReplayRegisterLayout {
    fn from_prepared(prepared: Option<&SsaArtifact>) -> Self {
        let Some(prepared) = prepared else {
            return Self::default();
        };

        let mut by_name = BTreeMap::new();
        let mut alias_candidates = BTreeMap::new();
        let mut record_var = |var: &r2ssa::SSAVar| {
            if !var.is_register() || var.version != 0 {
                return;
            }
            let bits = var.size * 8;
            let display_name = var.display_name();
            by_name
                .entry(display_name.to_ascii_uppercase())
                .or_insert_with(|| (display_name.clone(), bits));
            let base_name = var.name.strip_prefix("reg:").unwrap_or(&var.name);
            by_name
                .entry(base_name.to_ascii_uppercase())
                .or_insert_with(|| (display_name.clone(), bits));
            if let Some(alias) = register_alias_spec(base_name) {
                alias_candidates
                    .entry(display_name)
                    .or_insert((bits, alias));
            }
        };

        for block in prepared.blocks() {
            block.for_each_def(|def| record_var(def.var));
            block.for_each_source(|src| record_var(src.var));
        }

        Self {
            by_name,
            alias_candidates,
        }
    }

    fn resolve_register(&self, name: &str) -> Option<(String, u32)> {
        let key = name.trim().to_ascii_uppercase();
        self.by_name
            .get(&key)
            .cloned()
            .or_else(|| self.resolve_alias_register(&key))
    }

    fn resolve_alias_register(&self, name: &str) -> Option<(String, u32)> {
        let requested = register_alias_spec(name)?;
        let requested_low = requested.offset_bits;
        let requested_high = requested.offset_bits + requested.width_bits;

        let mut best: Option<(u8, u32, String, u32)> = None;
        for (display_name, (bits, candidate)) in &self.alias_candidates {
            if candidate.family != requested.family {
                continue;
            }

            let candidate_low = candidate.offset_bits;
            let candidate_high = candidate.offset_bits + candidate.width_bits;
            let relation_score =
                if candidate_low == requested_low && candidate.width_bits == requested.width_bits {
                    3
                } else if candidate_low <= requested_low && candidate_high >= requested_high {
                    2
                } else if candidate_low == requested_low {
                    1
                } else {
                    0
                };
            if relation_score == 0 {
                continue;
            }

            let width_distance = candidate.width_bits.abs_diff(requested.width_bits);
            let should_replace =
                best.as_ref()
                    .is_none_or(|(best_score, best_distance, _, best_bits)| {
                        relation_score > *best_score
                            || (relation_score == *best_score && width_distance < *best_distance)
                            || (relation_score == *best_score
                                && width_distance == *best_distance
                                && *bits > *best_bits)
                    });
            if should_replace {
                best = Some((relation_score, width_distance, display_name.clone(), *bits));
            }
        }

        best.map(|(_, _, display_name, bits)| (display_name, bits))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RegisterAliasSpec {
    family: Cow<'static, str>,
    offset_bits: u32,
    width_bits: u32,
}

fn register_alias_spec(base: &str) -> Option<RegisterAliasSpec> {
    let upper = base.to_ascii_uppercase();
    let base = upper.as_str();
    let fixed = match base {
        "AL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RAX"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "AH" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RAX"),
            offset_bits: 8,
            width_bits: 8,
        }),
        "AX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RAX"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "EAX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RAX"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RAX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RAX"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "BL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBX"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "BH" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBX"),
            offset_bits: 8,
            width_bits: 8,
        }),
        "BX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBX"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "EBX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBX"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RBX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBX"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "CL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RCX"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "CH" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RCX"),
            offset_bits: 8,
            width_bits: 8,
        }),
        "CX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RCX"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "ECX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RCX"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RCX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RCX"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "DL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDX"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "DH" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDX"),
            offset_bits: 8,
            width_bits: 8,
        }),
        "DX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDX"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "EDX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDX"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RDX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDX"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "SIL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSI"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "SI" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSI"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "ESI" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSI"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RSI" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSI"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "DIL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDI"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "DI" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDI"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "EDI" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDI"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RDI" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDI"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "BPL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBP"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "BP" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBP"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "EBP" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBP"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RBP" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBP"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "SPL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSP"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "SP" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSP"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "ESP" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSP"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RSP" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSP"),
            offset_bits: 0,
            width_bits: 64,
        }),
        _ => None,
    };
    if fixed.is_some() {
        return fixed;
    }

    parse_numbered_x86_register_alias(base)
}

fn parse_numbered_x86_register_alias(base: &str) -> Option<RegisterAliasSpec> {
    let (family, width_bits) = if let Some(family) = base.strip_suffix('B') {
        (family.to_string(), 8)
    } else if let Some(family) = base.strip_suffix('W') {
        (family.to_string(), 16)
    } else if let Some(family) = base.strip_suffix('D') {
        (family.to_string(), 32)
    } else {
        (base.to_string(), 64)
    };

    if !family.starts_with('R') {
        return None;
    }
    let digits = &family[1..];
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }

    Some(RegisterAliasSpec {
        family: Cow::Owned(family),
        offset_bits: 0,
        width_bits,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::SymValue;
    use r2il::{AddressSpace, ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};
    use r2ssa::{SourceAbiParameterSpec, SourceFunctionInterface, SourceFunctionReturn};
    use z3::Context;

    fn exact_replay_artifact() -> SsaArtifact {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_space(AddressSpace::ram(8));
        arch.add_register(RegisterDef::new("ACC", 0, 8));
        arch.add_register(RegisterDef::new("ACC32", 0, 4));
        arch.add_register(RegisterDef::new("IDX", 8, 8));
        arch.add_register(RegisterDef::new("UNUSED", 16, 8));

        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::register(0, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x18, 8),
            src: Varnode::register(8, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let acc = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        let interface = SourceFunctionInterface::new_exact(
            b"r2sym-exact-replay".to_vec(),
            "sysv",
            [SourceAbiParameterSpec::new(0, acc)],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("exact replay interface");
        SsaArtifact::for_symbolic_with_interface(&[block], Some(&arch), interface)
            .expect("exact replay artifact")
    }

    #[test]
    fn replay_seed_imports_replay_regions_and_symbolic_overlays() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        let seed = ReplaySeed {
            checkpoint_id: Some(7),
            entry_pc: Some(0x4141),
            registers: vec![ReplayRegisterValue {
                name: "rax".to_string(),
                value: 0x1122,
            }],
            memory: vec![ReplayMemoryWindow {
                addr: 0x5000,
                bytes: vec![0x41, 0x42, 0x43, 0x44],
                label: Some("input_window".to_string()),
            }],
            register_overlays: vec![ReplayRegisterOverlay {
                name: "rbx".to_string(),
                symbol: "replay_rbx".to_string(),
            }],
            memory_overlays: vec![ReplayMemoryOverlay {
                addr: 0x5001,
                size: 2,
                name: "user_buf".to_string(),
            }],
            tty_fds: vec![0],
            skip_sleep_calls: true,
        };

        seed_replay_state_for_arch(&mut state, None, None, &seed);

        assert_eq!(state.pc(), 0x4141);
        assert_eq!(state.get_register("RAX").as_concrete(), Some(0x1122));
        assert!(state.get_register("RBX").is_symbolic());
        let concrete = state.mem_read(&SymValue::concrete(0x5000, 64), 1);
        assert_eq!(concrete.as_concrete(), Some(0x41));
        let symbolic = state.mem_read(&SymValue::concrete(0x5001, 64), 2);
        assert!(symbolic.is_symbolic());
        assert!(state.is_tty_fd(0));
        assert!(state.skip_sleep_calls());
    }

    #[test]
    fn stable_replay_seed_fingerprint_is_order_and_case_stable() {
        let seed_a = ReplaySeed {
            checkpoint_id: Some(7),
            entry_pc: Some(0x4141),
            registers: vec![
                ReplayRegisterValue {
                    name: "rax".to_string(),
                    value: 0x1122,
                },
                ReplayRegisterValue {
                    name: "rdi".to_string(),
                    value: 0x3344,
                },
            ],
            memory: vec![
                ReplayMemoryWindow {
                    addr: 0x5000,
                    bytes: vec![0x41, 0x42],
                    label: Some("input".to_string()),
                },
                ReplayMemoryWindow {
                    addr: 0x6000,
                    bytes: vec![0x51, 0x52],
                    label: None,
                },
            ],
            register_overlays: vec![ReplayRegisterOverlay {
                name: "rbx".to_string(),
                symbol: "replay_rbx".to_string(),
            }],
            memory_overlays: vec![ReplayMemoryOverlay {
                addr: 0x5001,
                size: 2,
                name: "user_buf".to_string(),
            }],
            tty_fds: vec![1, 0],
            skip_sleep_calls: true,
        };
        let seed_b = ReplaySeed {
            checkpoint_id: Some(7),
            entry_pc: Some(0x4141),
            registers: vec![
                ReplayRegisterValue {
                    name: "RDI".to_string(),
                    value: 0x3344,
                },
                ReplayRegisterValue {
                    name: "RAX".to_string(),
                    value: 0x1122,
                },
            ],
            memory: vec![
                ReplayMemoryWindow {
                    addr: 0x6000,
                    bytes: vec![0x51, 0x52],
                    label: Some(String::new()),
                },
                ReplayMemoryWindow {
                    addr: 0x5000,
                    bytes: vec![0x41, 0x42],
                    label: Some(" input ".to_string()),
                },
            ],
            register_overlays: vec![ReplayRegisterOverlay {
                name: "RBX".to_string(),
                symbol: "replay_rbx".to_string(),
            }],
            memory_overlays: vec![ReplayMemoryOverlay {
                addr: 0x5001,
                size: 2,
                name: "user_buf".to_string(),
            }],
            tty_fds: vec![0, 1],
            skip_sleep_calls: true,
        };

        assert_eq!(
            stable_replay_seed_fingerprint(&seed_a),
            stable_replay_seed_fingerprint(&seed_b)
        );
    }

    #[test]
    fn stable_replay_seed_fingerprint_changes_with_seed_content() {
        let base = ReplaySeed {
            entry_pc: Some(0x4141),
            registers: vec![ReplayRegisterValue {
                name: "rax".to_string(),
                value: 0x1122,
            }],
            ..ReplaySeed::default()
        };
        let different = ReplaySeed {
            entry_pc: Some(0x4142),
            ..base.clone()
        };

        assert_ne!(
            stable_replay_seed_fingerprint(&base),
            stable_replay_seed_fingerprint(&different)
        );
    }

    #[test]
    fn prepared_replay_binds_source_storage_before_state_projection() {
        let prepared = exact_replay_artifact();
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        let seed = ReplaySeed {
            registers: vec![ReplayRegisterValue {
                name: "acc".to_string(),
                value: 0x1122,
            }],
            register_overlays: vec![ReplayRegisterOverlay {
                name: "idx".to_string(),
                symbol: "replay_idx".to_string(),
            }],
            ..ReplaySeed::default()
        };

        apply_replay_seed_to_prepared(&mut state, &prepared, &seed)
            .expect("source-owned replay binding");

        assert_eq!(state.get_register("ACC_0").as_concrete(), Some(0x1122));
        assert!(state.get_register("IDX_0").is_symbolic());
    }

    #[test]
    fn prepared_replay_refuses_unknown_and_overlapping_register_inputs_atomically() {
        let prepared = exact_replay_artifact();
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        let unknown = ReplaySeed {
            entry_pc: Some(0x2000),
            registers: vec![ReplayRegisterValue {
                name: "RAX".to_string(),
                value: 1,
            }],
            ..ReplaySeed::default()
        };
        assert!(matches!(
            apply_replay_seed_to_prepared(&mut state, &prepared, &unknown),
            Err(PreparedReplaySeedError::UnknownRegister(name)) if name == "RAX"
        ));
        assert_eq!(state.pc(), 0x1000);

        let overlapping = ReplaySeed {
            registers: vec![
                ReplayRegisterValue {
                    name: "ACC".to_string(),
                    value: 1,
                },
                ReplayRegisterValue {
                    name: "ACC32".to_string(),
                    value: 2,
                },
            ],
            ..ReplaySeed::default()
        };
        assert!(matches!(
            apply_replay_seed_to_prepared(&mut state, &prepared, &overlapping),
            Err(PreparedReplaySeedError::ConflictingRegisterLocation { .. })
        ));
        assert!(state.registers().is_empty());
    }

    #[test]
    fn prepared_replay_refuses_source_storage_without_an_entry_value() {
        let prepared = exact_replay_artifact();
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        let seed = ReplaySeed {
            register_overlays: vec![ReplayRegisterOverlay {
                name: "UNUSED".to_string(),
                symbol: "must_not_exist".to_string(),
            }],
            ..ReplaySeed::default()
        };
        let unused = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 16,
            size: 8,
        };

        assert_eq!(
            apply_replay_seed_to_prepared(&mut state, &prepared, &seed),
            Err(PreparedReplaySeedError::MissingEntryValue(unused))
        );
        assert!(state.registers().is_empty());
    }
}
