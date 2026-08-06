enum CExpr {
    IntLit(i32),
    Var(&'static str),
    Assign(Box<CExpr>, Box<CExpr>),
}

enum CStmt {
    Comment(String),
    Block(Vec<CStmt>),
    Expr(CExpr),
    Return(Option<CExpr>),
    If {
        cond: CExpr,
        then_body: Box<CStmt>,
        else_body: Option<Box<CStmt>>,
    },
    While {
        cond: CExpr,
        body: Box<CStmt>,
    },
    For {
        init: Option<Box<CStmt>>,
        body: Box<CStmt>,
    },
    Switch {
        expr: CExpr,
        cases: Vec<CStmt>,
    },
}

impl CStmt {
    fn comment(text: impl Into<String>) -> Self {
        Self::Comment(text.into())
    }
}

fn bad_summary_body() -> Vec<CStmt> {
    vec![
        CStmt::Return(Some(CExpr::IntLit(1))),
        CStmt::If {
            cond: CExpr::Var("summary_cond"),
            then_body: Box::new(CStmt::comment("then fact")),
            else_body: None,
        },
        CStmt::While {
            cond: CExpr::Var("summary_loop"),
            body: Box::new(CStmt::comment("loop fact")),
        },
        CStmt::For {
            init: None,
            body: Box::new(CStmt::comment("for fact")),
        },
        CStmt::Switch {
            expr: CExpr::Var("summary_selector"),
            cases: vec![CStmt::comment("case fact")],
        },
        CStmt::Expr(CExpr::Assign(
            Box::new(CExpr::Var("summary_dst")),
            Box::new(CExpr::IntLit(1)),
        )),
        CStmt::comment("allowed summary fact"),
    ]
}

fn main() {
    let _ = bad_summary_body();
}
