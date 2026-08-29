/// Proof that a refusal was decided through a constructor.
///
/// The field is private to this module, so no other module can name it and no
/// other module can build a refusal without going through the constructors
/// below. That is the whole point: instrumenting construction sites by hand
/// left holes, twice, and a refusal that escaped the instrumentation cost a
/// full pass to find each time. Now the compiler enumerates them.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct RefusalOrigin(());

impl std::fmt::Debug for RefusalOrigin {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

/// Defensive renderer result for operations whose canonical disposition is
/// owned by `r2ssa::MachineProjection`.
///
/// This is not a second support classifier: production must already have
/// received `MachineBuildError::UnsupportedOperation` from the projection.
/// The renderer result exists only so legacy helpers cannot turn an opaque
/// operation into executable C when called directly.
///
/// Every variant carries a witness that only this module can make, so a
/// refusal cannot be built without the constructor that records where it was
/// decided. `R2DEC_TRACE_REFUSAL` prints that.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum OpLoweringRefusal {
    MissingMachineProjectionAuthorization(RefusalOrigin),
    MissingProgramVariableAuthorization(RefusalOrigin),
    UnrepresentableOperation(RefusalOrigin),
}

impl std::fmt::Debug for OpLoweringRefusal {
    /// Named as it always was. The witness the variants carry is a
    /// construction guard, not information, and it reaches rendered residual
    /// comments through this.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::MissingMachineProjectionAuthorization(_) => {
                "MissingMachineProjectionAuthorization"
            }
            Self::MissingProgramVariableAuthorization(_) => "MissingProgramVariableAuthorization",
            Self::UnrepresentableOperation(_) => "UnrepresentableOperation",
        })
    }
}

impl OpLoweringRefusal {
    #[track_caller]
    fn note(name: &str) -> RefusalOrigin {
        if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
            eprintln!(
                "refusal {name} decided at {}",
                std::panic::Location::caller()
            );
        }
        RefusalOrigin(())
    }

    #[track_caller]
    pub(crate) fn missing_machine_projection() -> Self {
        Self::MissingMachineProjectionAuthorization(Self::note("machine-projection"))
    }

    #[track_caller]
    pub(crate) fn missing_program_variable() -> Self {
        Self::MissingProgramVariableAuthorization(Self::note("program-variable"))
    }

    #[track_caller]
    pub(crate) fn unrepresentable_operation() -> Self {
        Self::UnrepresentableOperation(Self::note("unrepresentable-operation"))
    }
}
