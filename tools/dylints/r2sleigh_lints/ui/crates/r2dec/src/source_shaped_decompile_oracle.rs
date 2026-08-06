struct SsaFunction;

struct Decompiler;

impl Decompiler {
    fn decompile(&self, _: &SsaFunction) -> String {
        String::new()
    }
}

enum CStmt {
    Return(i32),
}

mod tests {
    use super::{CStmt, Decompiler, SsaFunction};

    fn bad_return_shape_oracle() {
        let decompiler = Decompiler;
        let func = SsaFunction;
        let output = decompiler.decompile(&func);
        assert!(output.contains("return 1;"));
    }

    fn bad_if_shape_oracle() {
        let decompiler = Decompiler;
        let func = SsaFunction;
        let first = decompiler.decompile(&func);
        assert!(first.contains("if (arg1 != 19)"));
    }

    fn allowed_negative_residual_oracle() {
        let decompiler = Decompiler;
        let func = SsaFunction;
        let output = decompiler.decompile(&func);
        assert!(!output.contains("return summary_value;"));
    }

    fn allowed_non_source_text_oracle() {
        let decompiler = Decompiler;
        let func = SsaFunction;
        let output = decompiler.decompile(&func);
        assert!(output.contains("semantic summary"));
    }

    fn allowed_fold_or_ast_oracle() {
        let stmt = CStmt::Return(1);
        assert!(matches!(stmt, CStmt::Return(1)));
    }
}

fn main() {}
