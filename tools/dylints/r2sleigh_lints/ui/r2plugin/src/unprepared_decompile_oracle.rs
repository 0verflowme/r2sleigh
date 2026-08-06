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

fn bad_prepared_oracle(decompiler: &Decompiler, artifact: AnalysisArtifact) {
    let input = decompiler_input_from_artifact(artifact);
    let _ = decompiler.decompile_input(&input);
}

mod tests {
    use super::{
        decompiler_input_from_artifact, AnalysisArtifact, Decompiler, SsaFunction,
    };

    fn bad_prepared_executable_c_oracle() {
        let decompiler = Decompiler;
        let artifact = AnalysisArtifact {
            ssa_func: SsaFunction,
        };
        let input = decompiler_input_from_artifact(artifact);
        let output = decompiler.decompile_input(&input);
        assert!(output.contains("return 1;"));
    }
}

fn allowed_raw_ssa_unit_test(decompiler: &Decompiler, func: SsaFunction) {
    let _ = decompiler.decompile(&func);
}

fn main() {}
