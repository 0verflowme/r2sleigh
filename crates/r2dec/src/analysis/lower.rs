/// Proof that a refusal was decided through a constructor, and where.
///
/// The field is private to this module, so no other module can name it and no
/// other module can build a refusal without going through the constructors
/// below. That is the whole point: instrumenting construction sites by hand
/// left holes, twice, and a refusal that escaped the instrumentation cost a
/// full pass to find each time. Now the compiler enumerates them.
///
/// The witness also carries where it was made, and takes it from
/// `#[track_caller]` rather than from an argument. Naming seventy-two
/// construction sites by hand would have been the same mistake in a new place:
/// one unnamed site is one refusal that reports nothing. A caller location is
/// a `&'static` reference, so carrying it is free, and it separates causes that
/// were previously one word -- on `/bin/ls` a single count of seven "op
/// lowering" refusals turned out to be an incomplete return boundary and a call
/// whose arguments could not be spelled, at two different lines.
///
/// What the predicate compared is a different thing and does not travel here:
/// it is unbounded and only wanted when someone is looking, which is what
/// `refusal_evidence!` prints.
#[derive(Clone, Copy, Eq)]
pub(crate) struct RefusalOrigin(&'static std::panic::Location<'static>);

impl RefusalOrigin {
    pub(crate) const fn site(self) -> &'static std::panic::Location<'static> {
        self.0
    }
}

/// Two refusals of the same kind are the same refusal.
///
/// The site is diagnostic. Comparing it would make a refusal's identity depend
/// on which predicate happened to decide it, which is not what any caller means
/// when it asks whether two refusals are equal, and would make every equality
/// assertion in the tree brittle against moving a line.
impl PartialEq for RefusalOrigin {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl std::hash::Hash for RefusalOrigin {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

impl std::fmt::Debug for RefusalOrigin {
    /// The file's own name and the line, not the path.
    ///
    /// This reaches rendered residual comments, where a repository-relative
    /// path is noise and the pair that identifies the predicate is not.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let file = self.0.file();
        let base = file.rsplit('/').next().unwrap_or(file);
        write!(f, "{base}:{}", self.0.line())
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
    /// The kind, then the site that decided it.
    ///
    /// The site reaches rendered residual comments through this, which is the
    /// point: a reader who sees `op lowering` learns nothing, and a reader who
    /// sees `op lowering: return-boundary` knows which predicate to open.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (kind, origin) = match self {
            Self::MissingMachineProjectionAuthorization(origin) => {
                ("MissingMachineProjectionAuthorization", origin)
            }
            Self::MissingProgramVariableAuthorization(origin) => {
                ("MissingProgramVariableAuthorization", origin)
            }
            Self::UnrepresentableOperation(origin) => ("UnrepresentableOperation", origin),
        };
        write!(f, "{kind}({origin:?})")
    }
}

impl OpLoweringRefusal {
    #[track_caller]
    fn note(kind: &str) -> RefusalOrigin {
        let origin = RefusalOrigin(std::panic::Location::caller());
        if r2il::refusal_evidence::tracing() {
            eprintln!("refusal {kind} decided at {}", origin.0);
        }
        origin
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
