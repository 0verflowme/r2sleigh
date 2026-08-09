//! Closed semantic-C composition for one exact unsigned counted loop.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_COUNTED_LOOP_TERMINAL_RETURN_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedClosedCountedLoopControl, CertifiedMachineFunction, CertifiedRenderPermit,
    CertifiedTypedRegionKind, EffectDisposition, RenderAuthorizationError, TypedRegionMapping,
    certify_counted_loop_terminal_return_region,
};
use r2ssa::{CanonicalInstructionId, MachineBuildError, SemanticObligationId, SsaArtifact};
use serde::Serialize;

use crate::semantic_c::value_name;

pub const CERTIFIED_COUNTED_LOOP_RETURN_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_COUNTED_LOOP_TERMINAL_RETURN_CONTRACT_VERSION;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CountedLoopReturnFunctionScope {
    ClosedUnsignedZeroInitializedUnitIncrementCounterAndTerminalCarrierReturn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum CountedLoopPhaseKind {
    Initializer,
    Condition,
    BodyUpdate,
    Return,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CountedLoopPhase {
    kind: CountedLoopPhaseKind,
    producer: CanonicalInstructionId,
}

impl CountedLoopPhase {
    pub const fn kind(&self) -> CountedLoopPhaseKind {
        self.kind
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedCountedLoopReturnFunction {
    schema_version: u32,
    scope: CountedLoopReturnFunctionScope,
    name: String,
    origin: CertifiedArtifactOrigin,
    control: CertifiedClosedCountedLoopControl,
    phases: Box<[CountedLoopPhase]>,
    mappings: Box<[TypedRegionMapping]>,
    render_permit: CertifiedRenderPermit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CountedLoopReturnFunctionError {
    Machine(MachineBuildError),
    Authorization(RenderAuthorizationError),
    MissingCountedLoopControl(u64),
    InvalidComposition(Vec<String>),
    InvalidWidth(u32),
}

impl std::fmt::Display for CountedLoopReturnFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "counted-loop return function failed: {self:?}")
    }
}

impl std::error::Error for CountedLoopReturnFunctionError {}

impl From<MachineBuildError> for CountedLoopReturnFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RenderAuthorizationError> for CountedLoopReturnFunctionError {
    fn from(error: RenderAuthorizationError) -> Self {
        Self::Authorization(error)
    }
}

impl CertifiedCountedLoopReturnFunction {
    pub fn from_artifact(artifact: &SsaArtifact) -> Result<Self, CountedLoopReturnFunctionError> {
        let certified = CertifiedMachineFunction::from_artifact(artifact)?;
        Self::from_certified(&certified)
    }

    pub fn from_certified(
        certified: &CertifiedMachineFunction,
    ) -> Result<Self, CountedLoopReturnFunctionError> {
        let preheader = certified.topology().entry_addr();
        let header = certified
            .topology()
            .block(preheader)
            .and_then(|block| match block.terminator() {
                r2cert::CertifiedSourceTerminator::Branch { target } => Some(*target),
                _ => None,
            })
            .ok_or(CountedLoopReturnFunctionError::MissingCountedLoopControl(
                preheader,
            ))?;
        let control = certified
            .closed_counted_loop_control_for_header(header)
            .cloned()
            .ok_or(CountedLoopReturnFunctionError::MissingCountedLoopControl(
                header,
            ))?;
        let phases = expected_phases(&control).into_boxed_slice();
        let mappings = certified
            .source()
            .obligations()
            .keys()
            .map(|obligation| {
                let [effect] = certified.ledger().effects(*obligation) else {
                    return Err(RenderAuthorizationError::IncompleteLedger);
                };
                Ok(TypedRegionMapping::new(
                    *obligation,
                    effect.disposition().clone(),
                ))
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_boxed_slice();
        let render_permit = certify_counted_loop_terminal_return_region(
            certified.origin(),
            certified.ledger(),
            mappings.iter().cloned(),
            &control,
        )?;
        let function = Self {
            schema_version: CERTIFIED_COUNTED_LOOP_RETURN_FUNCTION_SCHEMA_VERSION,
            scope: CountedLoopReturnFunctionScope::ClosedUnsignedZeroInitializedUnitIncrementCounterAndTerminalCarrierReturn,
            name: format!("certified_sub_{preheader:x}"),
            origin: certified.origin().clone(),
            control,
            phases,
            mappings,
            render_permit,
        };
        let report = function.audit();
        if !report.has_exact_counted_loop_return() {
            return Err(CountedLoopReturnFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> CountedLoopReturnFunctionScope {
        self.scope
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn control(&self) -> &CertifiedClosedCountedLoopControl {
        &self.control
    }

    pub const fn phases(&self) -> &[CountedLoopPhase] {
        &self.phases
    }

    pub const fn mappings(&self) -> &[TypedRegionMapping] {
        &self.mappings
    }

    pub const fn render_permit(&self) -> &CertifiedRenderPermit {
        &self.render_permit
    }

    pub fn audit(&self) -> CountedLoopReturnFunctionAuditReport {
        let mut invalid = Vec::new();
        if self.schema_version != CERTIFIED_COUNTED_LOOP_RETURN_FUNCTION_SCHEMA_VERSION {
            invalid.push("counted-loop schema mismatch".to_string());
        }
        if self.scope
            != CountedLoopReturnFunctionScope::ClosedUnsignedZeroInitializedUnitIncrementCounterAndTerminalCarrierReturn
        {
            invalid.push("counted-loop scope mismatch".to_string());
        }
        if self.control.origin() != &self.origin || self.control.state().origin() != &self.origin {
            invalid.push("counted-loop children do not share one artifact origin".to_string());
        }
        if self.phases.as_ref() != expected_phases(&self.control).as_slice() {
            invalid.push(
                "initializer, condition, body update, and return phases are not exact and ordered"
                    .to_string(),
            );
        }
        let phase_counts = counts(self.phases.iter().map(CountedLoopPhase::kind));
        if phase_counts.len() != 4 || phase_counts.values().any(|count| *count != 1) {
            invalid.push("counted-loop phases are missing or duplicated".to_string());
        }
        let expected_obligations = self
            .origin
            .source()
            .obligations()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let mapping_counts = counts(self.mappings.iter().map(TypedRegionMapping::obligation));
        let actual_obligations = mapping_counts.keys().copied().collect::<BTreeSet<_>>();
        let missing = expected_obligations
            .difference(&actual_obligations)
            .copied()
            .collect();
        let unexpected = actual_obligations
            .difference(&expected_obligations)
            .copied()
            .collect();
        let duplicate = mapping_counts
            .iter()
            .filter_map(|(obligation, count)| (*count > 1).then_some(*obligation))
            .collect();
        if self.mappings.len() != expected_obligations.len()
            || self.mappings.iter().any(|mapping| {
                matches!(
                    mapping.source_disposition(),
                    EffectDisposition::Residualized { .. } | EffectDisposition::Refused { .. }
                )
            })
        {
            invalid.push("counted-loop manifest is not exact and closed".to_string());
        }
        if !self.render_permit.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::CountedLoopTerminalReturnFunction,
            CERTIFIED_COUNTED_LOOP_RETURN_FUNCTION_SCHEMA_VERSION,
            &self.mappings,
        ) {
            invalid.push("counted-loop render permit does not match its manifest".to_string());
        }
        CountedLoopReturnFunctionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
        }
    }

    pub fn render_certified_c(&self) -> Result<String, CountedLoopReturnFunctionError> {
        let report = self.audit();
        if !report.has_exact_counted_loop_return() || !self.render_permit.authorizes_certified_c() {
            return Err(CountedLoopReturnFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        let state = self.control.state();
        let width = state.phi().binding().width_bits();
        let ty = uint_type(width)?;
        let macro_name = uint_macro(width)?;
        let counter = value_name(state.phi().binding());
        let bound = value_name(state.bound().binding());
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        writeln!(&mut output, "{ty} {}({ty} {bound}) {{", self.name)
            .expect("String writes cannot fail");
        writeln!(&mut output, "\t{ty} {counter} = {macro_name}(0x0);")
            .expect("String writes cannot fail");
        writeln!(&mut output, "\twhile ({counter} < {bound}) {{")
            .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\t\t{counter} = ({ty})({counter} + {macro_name}(0x1));"
        )
        .expect("String writes cannot fail");
        output.push_str("\t}\n");
        writeln!(&mut output, "\treturn {counter};").expect("String writes cannot fail");
        output.push_str("}\n");
        Ok(output)
    }
}

fn expected_phases(control: &CertifiedClosedCountedLoopControl) -> Vec<CountedLoopPhase> {
    vec![
        CountedLoopPhase {
            kind: CountedLoopPhaseKind::Initializer,
            producer: control
                .state()
                .initializer()
                .producer()
                .expect("sealed initializer producer"),
        },
        CountedLoopPhase {
            kind: CountedLoopPhaseKind::Condition,
            producer: control
                .state()
                .condition()
                .producer()
                .expect("sealed condition producer"),
        },
        CountedLoopPhase {
            kind: CountedLoopPhaseKind::BodyUpdate,
            producer: control
                .state()
                .update()
                .producer()
                .expect("sealed update producer"),
        },
        CountedLoopPhase {
            kind: CountedLoopPhaseKind::Return,
            producer: control.return_control().producer(),
        },
    ]
}

fn uint_type(width: u32) -> Result<&'static str, CountedLoopReturnFunctionError> {
    match width {
        8 => Ok("uint8_t"),
        16 => Ok("uint16_t"),
        32 => Ok("uint32_t"),
        64 => Ok("uint64_t"),
        _ => Err(CountedLoopReturnFunctionError::InvalidWidth(width)),
    }
}

fn uint_macro(width: u32) -> Result<&'static str, CountedLoopReturnFunctionError> {
    match width {
        8 => Ok("UINT8_C"),
        16 => Ok("UINT16_C"),
        32 => Ok("UINT32_C"),
        64 => Ok("UINT64_C"),
        _ => Err(CountedLoopReturnFunctionError::InvalidWidth(width)),
    }
}

fn counts<T: Ord>(values: impl IntoIterator<Item = T>) -> BTreeMap<T, usize> {
    let mut counts = BTreeMap::new();
    for value in values {
        *counts.entry(value).or_default() += 1;
    }
    counts
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CountedLoopReturnFunctionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
}

impl CountedLoopReturnFunctionAuditReport {
    pub fn has_exact_counted_loop_return(&self) -> bool {
        self.missing.is_empty()
            && self.duplicate.is_empty()
            && self.unexpected.is_empty()
            && self.invalid.is_empty()
    }

    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CountedLoopExecutionOutcome {
    Returned { counter: u64, iterations: u32 },
    BoundExhausted { counter: u64, iterations: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CountedLoopDifferentialCase {
    bound: u64,
    source: CountedLoopExecutionOutcome,
    certified: CountedLoopExecutionOutcome,
    rendered: CountedLoopExecutionOutcome,
}

impl CountedLoopDifferentialCase {
    pub const fn bound(&self) -> u64 {
        self.bound
    }

    pub const fn source(&self) -> CountedLoopExecutionOutcome {
        self.source
    }

    pub const fn certified(&self) -> CountedLoopExecutionOutcome {
        self.certified
    }

    pub const fn rendered(&self) -> CountedLoopExecutionOutcome {
        self.rendered
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CountedLoopDifferentialReport {
    cases: Box<[CountedLoopDifferentialCase]>,
}

impl CountedLoopDifferentialReport {
    pub const fn cases(&self) -> &[CountedLoopDifferentialCase] {
        &self.cases
    }

    pub fn all_match(&self) -> bool {
        self.cases
            .iter()
            .all(|case| case.source == case.certified && case.source == case.rendered)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CountedProgram {
    width: u32,
    initializer: u64,
    increment: u64,
}

pub fn check_counted_loop_return_differential(
    artifact: &SsaArtifact,
    max_iterations: u32,
) -> Result<CountedLoopDifferentialReport, String> {
    if max_iterations < 3 {
        return Err("counted-loop differential budget is below three".to_string());
    }
    let function = CertifiedCountedLoopReturnFunction::from_artifact(artifact)
        .map_err(|error| format!("counted-loop candidate not admitted: {error}"))?;
    let rendered = function
        .render_certified_c()
        .map_err(|error| format!("counted-loop rendering failed: {error}"))?;
    let source_program = source_program(artifact)?;
    let certified_program = CountedProgram {
        width: function.control.state().phi().binding().width_bits(),
        initializer: 0,
        increment: 1,
    };
    let rendered_program = rendered_program(&function, &rendered)?;
    let exhausted_bound = u64::from(max_iterations).saturating_add(1);
    let max_bound = if source_program.width == 64 {
        u64::MAX
    } else {
        (1_u64 << source_program.width) - 1
    };
    if exhausted_bound > max_bound {
        return Err("counted-loop differential budget exceeds the admitted width".to_string());
    }
    let mut cases = Vec::new();
    for bound in [0, 1, 3, exhausted_bound] {
        cases.push(CountedLoopDifferentialCase {
            bound,
            source: execute_counted(source_program, bound, max_iterations),
            certified: execute_counted(certified_program, bound, max_iterations),
            rendered: execute_counted(rendered_program, bound, max_iterations),
        });
    }
    let report = CountedLoopDifferentialReport {
        cases: cases.into_boxed_slice(),
    };
    if !report.all_match() {
        return Err("counted-loop differential mismatch".to_string());
    }
    Ok(report)
}

fn source_program(artifact: &SsaArtifact) -> Result<CountedProgram, String> {
    let facts = artifact
        .structured()
        .canonical_counted_loops
        .values()
        .collect::<Vec<_>>();
    let [fact] = facts.as_slice() else {
        return Err("source has no unique canonical counted loop".to_string());
    };
    let initializer = artifact
        .graph()
        .inst(fact.initializer_inst)
        .and_then(|instruction| instruction.inputs.first())
        .and_then(|value| artifact.graph().value(*value))
        .and_then(|value| value.var.constant_bits())
        .ok_or_else(|| "source initializer is not exact".to_string())?;
    let increment = artifact
        .graph()
        .inst(fact.update_inst)
        .and_then(|instruction| instruction.inputs.get(1))
        .and_then(|value| artifact.graph().value(*value))
        .and_then(|value| value.var.constant_bits())
        .ok_or_else(|| "source increment is not exact".to_string())?;
    Ok(CountedProgram {
        width: fact.width.saturating_mul(8),
        initializer,
        increment,
    })
}

fn rendered_program(
    function: &CertifiedCountedLoopReturnFunction,
    rendered: &str,
) -> Result<CountedProgram, String> {
    let state = function.control.state();
    let width = state.phi().binding().width_bits();
    let ty = uint_type(width).map_err(|error| error.to_string())?;
    let macro_name = uint_macro(width).map_err(|error| error.to_string())?;
    let counter = value_name(state.phi().binding());
    let bound = value_name(state.bound().binding());
    let expected = [
        format!("\t{ty} {counter} = {macro_name}(0x0);"),
        format!("\twhile ({counter} < {bound}) {{"),
        format!("\t\t{counter} = ({ty})({counter} + {macro_name}(0x1));"),
        format!("\treturn {counter};"),
    ];
    if expected
        .iter()
        .any(|expected| rendered.lines().filter(|line| line == expected).count() != 1)
    {
        return Err("rendered counted-loop phases are malformed or duplicated".to_string());
    }
    Ok(CountedProgram {
        width,
        initializer: 0,
        increment: 1,
    })
}

fn execute_counted(
    program: CountedProgram,
    bound: u64,
    max_iterations: u32,
) -> CountedLoopExecutionOutcome {
    let mask = if program.width == 64 {
        u64::MAX
    } else {
        (1_u64 << program.width) - 1
    };
    let bound = bound & mask;
    let mut counter = program.initializer & mask;
    for iterations in 0..max_iterations {
        if counter >= bound {
            return CountedLoopExecutionOutcome::Returned {
                counter,
                iterations,
            };
        }
        counter = counter.wrapping_add(program.increment) & mask;
    }
    if counter >= bound {
        CountedLoopExecutionOutcome::Returned {
            counter,
            iterations: max_iterations,
        }
    } else {
        CountedLoopExecutionOutcome::BoundExhausted {
            counter,
            iterations: max_iterations,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceFunctionInterface,
        SourceFunctionReturn,
    };

    fn storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn artifact() -> SsaArtifact {
        let counter = Varnode::register(0, 8);
        let mut preheader = R2ILBlock::new(0xb000, 4);
        preheader.push(R2ILOp::Copy {
            dst: counter.clone(),
            src: Varnode::constant(0, 8),
        });
        preheader.push(R2ILOp::Branch {
            target: Varnode::ram(0xb010, 8),
        });
        let condition = Varnode::unique(0x40, 1);
        let mut header = R2ILBlock::new(0xb010, 4);
        header.push(R2ILOp::IntLess {
            dst: condition.clone(),
            a: counter.clone(),
            b: Varnode::register(8, 8),
        });
        header.push(R2ILOp::CBranch {
            target: Varnode::ram(0xb020, 8),
            cond: condition,
        });
        let mut exit = R2ILBlock::new(0xb014, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let mut latch = R2ILBlock::new(0xb020, 4);
        latch.push(R2ILOp::IntAdd {
            dst: counter.clone(),
            a: counter,
            b: Varnode::constant(1, 8),
        });
        latch.push(R2ILOp::Branch {
            target: Varnode::ram(0xb010, 8),
        });
        let mut arch = ArchSpec::new("counted-loop-return-test");
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rip", 16, 8));
        let interface = SourceFunctionInterface::new(
            b"counted-loop-return-revision-1".to_vec(),
            "test-register-abi",
            [SourceAbiParameterSpec::new(0, storage(8))],
            SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
        )
        .expect("counted-loop interface");
        SsaArtifact::raw_with_interface(&[preheader, header, exit, latch], Some(&arch), interface)
            .expect("counted-loop artifact")
    }

    fn compile(source: &str) {
        let mut compiler = Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Wpedantic",
                "-Werror",
                "-fsyntax-only",
                "-x",
                "c",
                "-",
            ])
            .stdin(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("C compiler required");
        compiler
            .stdin
            .as_mut()
            .expect("compiler stdin")
            .write_all(source.as_bytes())
            .expect("write C source");
        let output = compiler.wait_with_output().expect("wait for compiler");
        assert!(
            output.status.success(),
            "generated C failed:\n{source}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn exact_counted_loop_authorizes_compiles_and_matches_bounded_differential() {
        let artifact = artifact();
        let function = CertifiedCountedLoopReturnFunction::from_artifact(&artifact)
            .expect("certified counted loop");
        assert!(function.audit().has_exact_counted_loop_return());
        assert!(function.render_permit().authorizes_certified_c());
        let source = function.render_certified_c().expect("counted-loop C");
        assert!(source.contains("while (v_"));
        assert!(source.contains(" + UINT64_C(0x1)"));
        compile(&source);
        let differential =
            check_counted_loop_return_differential(&artifact, 3).expect("counted differential");
        assert!(differential.all_match());
        assert_eq!(
            differential
                .cases()
                .iter()
                .map(CountedLoopDifferentialCase::bound)
                .collect::<Vec<_>>(),
            vec![0, 1, 3, 4]
        );
        assert!(matches!(
            differential.cases()[3].source(),
            CountedLoopExecutionOutcome::BoundExhausted {
                counter: 3,
                iterations: 3
            }
        ));
    }

    #[test]
    fn dropped_duplicated_or_reordered_loop_phases_fail_before_rendering() {
        let function = CertifiedCountedLoopReturnFunction::from_artifact(&artifact())
            .expect("certified counted loop");
        for dropped in 0..function.phases.len() {
            let mut corrupted = function.clone();
            let mut phases = corrupted.phases.to_vec();
            phases.remove(dropped);
            corrupted.phases = phases.into_boxed_slice();
            assert!(!corrupted.audit().has_exact_counted_loop_return());
            assert!(corrupted.render_certified_c().is_err());
        }

        let mut duplicated = function.clone();
        let mut phases = duplicated.phases.to_vec();
        phases.insert(2, phases[2]);
        duplicated.phases = phases.into_boxed_slice();
        assert!(!duplicated.audit().has_exact_counted_loop_return());
        assert!(duplicated.render_certified_c().is_err());

        let mut reordered = function;
        let mut phases = reordered.phases.to_vec();
        phases.swap(0, 1);
        reordered.phases = phases.into_boxed_slice();
        assert!(!reordered.audit().has_exact_counted_loop_return());
        assert!(reordered.render_certified_c().is_err());
    }
}
