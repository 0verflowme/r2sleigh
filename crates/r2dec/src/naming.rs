//! How a value is spelled, in one place.
//!
//! Several layers used to answer this question with their own copy of the rules,
//! and they disagreed: only one consulted the carrier map, they lowercased
//! differently, and some call sites skipped all of them and handed an SSA display
//! name straight to the symbol table. One value could end up with two identifiers.
//!
//! The precedence lives in `spell_var` and nowhere else. What differs between
//! layers is the tables they can see, so that is what `NameSource` carries.

use crate::analysis::utils::ssa_render_base_name;
use crate::analysis::utils::parse_const_value;
use r2ssa::SSAVar;

/// The tables a layer can consult when spelling a value.
pub(crate) trait NameSource {
    /// The sealed renderer binding for this exact SSA value.
    fn planned_binding_name(&self, _var: &SSAVar) -> Option<String> {
        None
    }

    /// The carrier this value belongs to, when it is part of one.
    fn carrier_alias(&self, display: &str) -> Option<String>;

    /// The merged name coalescing gave this value.
    fn var_alias(&self, display: &str) -> Option<String>;

    /// The argument name a register holds on entry.
    fn param_alias(&self, register: &str) -> Option<String>;

    /// The declared name for a frame slot an alias stands for.
    fn canonical_stack_name(&self, _alias: &str) -> Option<String> {
        None
    }
}

/// A layer that has no tables of its own.
pub(crate) struct NoNames;

impl NameSource for NoNames {
    fn carrier_alias(&self, _display: &str) -> Option<String> {
        None
    }

    fn var_alias(&self, _display: &str) -> Option<String> {
        None
    }

    fn param_alias(&self, _register: &str) -> Option<String> {
        None
    }
}

/// How this value is spelled.
pub(crate) fn spell_var(var: &SSAVar, source: &dyn NameSource) -> String {
    if var.is_const() {
        let value = parse_const_value(&var.name).unwrap_or(0);
        return crate::codegen::format_unsigned_literal(value);
    }

    let display = var.display_name();
    if let Some(binding) = source.planned_binding_name(var) {
        return binding;
    }
    // A carrier member is the carrier, except at version zero, which is the
    // value the function was entered with and keeps the argument's name.
    if var.version > 0
        && let Some(carrier) = source.carrier_alias(&display)
    {
        return carrier;
    }
    if let Some(alias) = source.var_alias(&display) {
        return source.canonical_stack_name(&alias).unwrap_or(alias);
    }
    if var.version == 0
        && let Some(alias) = source.param_alias(&var.name)
    {
        return alias;
    }

    let base = ssa_render_base_name(var);
    if var.version > 0 {
        format!("{}_{}", base, var.version)
    } else {
        base
    }
}
