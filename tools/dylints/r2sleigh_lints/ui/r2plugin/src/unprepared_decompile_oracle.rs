struct SsaFunction;

struct AnalysisArtifact {
    ssa_func: SsaFunction,
}

struct Decompiler;

impl Decompiler {
    fn decompile(&self, _: &SsaFunction) -> String {
        String::new()
    }

    fn decompile_input(&self, _: &DecompilerInput) -> String {
        String::new()
    }
}

struct DecompilerInput;

fn decompiler_input_from_artifact(_: AnalysisArtifact) -> DecompilerInput {
    DecompilerInput
}

fn bad_artifact_oracle(decompiler: &Decompiler, artifact: AnalysisArtifact) {
    let _ = decompiler.decompile(&artifact.ssa_func);
}

fn good_prepared_oracle(decompiler: &Decompiler, artifact: AnalysisArtifact) {
    let input = decompiler_input_from_artifact(artifact);
    let _ = decompiler.decompile_input(&input);
}

fn allowed_raw_ssa_unit_test(decompiler: &Decompiler, func: SsaFunction) {
    let _ = decompiler.decompile(&func);
}

fn main() {}
