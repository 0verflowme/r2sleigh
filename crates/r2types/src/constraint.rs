use std::hash::Hash;

use r2ssa::SSAVar;

use crate::model::TypeId;

/// A node of the type graph the solver assigns types to.
///
/// The solver is the same whether the nodes are SSA variables of one function
/// or the values, objects and slots of a prepared artifact, so the node type is
/// a parameter and only the label used in diagnostics differs.
pub trait SolverNode: Clone + Eq + Hash {
    fn solver_label(&self) -> String;
}

impl SolverNode for SSAVar {
    fn solver_label(&self) -> String {
        self.display_name()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConstraintSource {
    Inferred,
    SignatureRegistry,
    External,
}

impl ConstraintSource {
    pub fn priority(self) -> u8 {
        match self {
            Self::Inferred => 1,
            Self::SignatureRegistry => 2,
            Self::External => 3,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemoryCapability {
    Load,
    Store,
}

#[derive(Debug, Clone)]
pub enum Constraint<K = SSAVar> {
    SetType {
        var: K,
        ty: TypeId,
        source: ConstraintSource,
    },
    Equal {
        a: K,
        b: K,
        source: ConstraintSource,
    },
    Subtype {
        var: K,
        ty: TypeId,
        source: ConstraintSource,
    },
    HasCapability {
        ptr: K,
        capability: MemoryCapability,
        elem_ty: TypeId,
        source: ConstraintSource,
    },
    CallSig {
        target: K,
        args: Vec<K>,
        params: Vec<TypeId>,
        ret: Option<(K, TypeId)>,
        source: ConstraintSource,
    },
    FieldAccess {
        base_ptr: K,
        offset: u64,
        field_ty: TypeId,
        field_name: Option<String>,
        source: ConstraintSource,
    },
}

impl<K> Constraint<K> {
    pub fn source(&self) -> ConstraintSource {
        match self {
            Self::SetType { source, .. }
            | Self::Equal { source, .. }
            | Self::Subtype { source, .. }
            | Self::HasCapability { source, .. }
            | Self::CallSig { source, .. }
            | Self::FieldAccess { source, .. } => *source,
        }
    }
}
