enum CExpr {
    IntLit(i64),
    Var(String),
}

struct Block;

struct FoldCtx;

impl FoldCtx {
    fn extract_condition_from_block(&self, _: &Block) -> Option<CExpr> {
        None
    }
}

fn bad_unwrap_or_default_true(ctx: &FoldCtx, block: &Block) -> CExpr {
    ctx.extract_condition_from_block(block)
        .unwrap_or(CExpr::IntLit(1))
}

fn bad_unwrap_or_else_default_true(ctx: &FoldCtx, block: &Block) -> CExpr {
    ctx.extract_condition_from_block(block)
        .unwrap_or_else(|| CExpr::IntLit(1))
}

fn allowed_exact_true_condition() -> CExpr {
    CExpr::IntLit(1)
}

fn allowed_non_branch_fallback(value: Option<CExpr>) -> CExpr {
    value.unwrap_or(CExpr::IntLit(1))
}

fn allowed_unresolved_condition(ctx: &FoldCtx, block: &Block) -> CExpr {
    ctx.extract_condition_from_block(block)
        .unwrap_or_else(|| CExpr::Var("unresolved".to_string()))
}

fn main() {}
