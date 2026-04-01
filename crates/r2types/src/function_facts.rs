use crate::facts::FunctionTypeFacts;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionFacts {
    pub types: FunctionTypeFacts,
    pub semantics: Option<r2sym::SemanticArtifact>,
}

impl FunctionFacts {
    pub fn new(types: FunctionTypeFacts, semantics: Option<r2sym::SemanticArtifact>) -> Self {
        Self { types, semantics }
    }

    pub fn type_plan(&self) -> Option<r2sym::TypePlan> {
        self.semantics
            .as_ref()
            .map(r2sym::SemanticArtifact::type_plan)
    }

    pub fn decompile_plan(&self) -> Option<r2sym::DecompilePlan> {
        self.semantics
            .as_ref()
            .map(r2sym::SemanticArtifact::decompile_plan)
    }
}
