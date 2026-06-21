use std::fmt::Write as _;

struct InferredSignature {
    function_name: String,
    signature: String,
}

struct StructDecl {
    decl: String,
}

struct TypeWritebackPlan {
    signature: InferredSignature,
    struct_decls: Vec<StructDecl>,
}

fn render_semantic_worker_linearization(plan: &TypeWritebackPlan) -> String {
    let mut out = String::new();
    let _ = writeln!(&mut out, "{} {{", plan.signature.signature);
    for decl in &plan.struct_decls {
        let _ = writeln!(&mut out, "{}", decl.decl);
    }
    out
}

fn allowed_summary_fact_comments(plan: &TypeWritebackPlan) -> String {
    let mut out = String::new();
    let _ = writeln!(&mut out, "/* function: {} */", plan.signature.function_name);
    let _ = writeln!(
        &mut out,
        "/* type writeback declarations suppressed: {} */",
        plan.struct_decls.len()
    );
    out
}

fn main() {
    let plan = TypeWritebackPlan {
        signature: InferredSignature {
            function_name: "sym.worker".to_string(),
            signature: "int sym.worker(int argc)".to_string(),
        },
        struct_decls: vec![StructDecl {
            decl: "struct Fake { int field; };".to_string(),
        }],
    };
    let _ = render_semantic_worker_linearization(&plan);
    let _ = allowed_summary_fact_comments(&plan);
}
