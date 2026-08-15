use crate::blocks::BlockSlice;
use crate::{ArchSpec, R2ILBlock};
use std::ffi::{CStr, c_char};

#[repr(C)]
pub struct R2ILFunctionBlocks {
    pub(crate) entry_addr: u64,
    pub(crate) name: *const c_char,
    pub(crate) blocks: *const *const R2ILBlock,
    pub(crate) num_blocks: usize,
    pub(crate) provenance: u32,
}

const R2SLEIGH_SCOPED_FUNCTION_PROVENANCE_ANALYZED: u32 = 0;
const R2SLEIGH_SCOPED_FUNCTION_PROVENANCE_RUNTIME_MATERIALIZED: u32 = 1;

fn scoped_function_provenance_from_ffi(raw: u32) -> Option<r2sym::sim::ScopedFunctionProvenance> {
    match raw {
        R2SLEIGH_SCOPED_FUNCTION_PROVENANCE_ANALYZED => {
            Some(r2sym::sim::ScopedFunctionProvenance::Analyzed)
        }
        R2SLEIGH_SCOPED_FUNCTION_PROVENANCE_RUNTIME_MATERIALIZED => {
            Some(r2sym::sim::ScopedFunctionProvenance::RuntimeMaterialized)
        }
        _ => None,
    }
}

pub(crate) fn build_symbolic_prepared(
    blocks: &[R2ILBlock],
    arch: Option<&ArchSpec>,
    name: Option<&str>,
) -> Option<r2ssa::SsaArtifact> {
    let prepared = r2ssa::SsaArtifact::for_symbolic(blocks, arch)?;
    Some(match name {
        Some(name) if !name.is_empty() => prepared.with_name(name.to_string()),
        _ => prepared,
    })
}

pub(crate) unsafe fn build_symbolic_scope_from_ffi(
    functions: *const R2ILFunctionBlocks,
    num_functions: usize,
    arch: Option<&ArchSpec>,
    root_entry_addr: u64,
) -> Option<r2sym::PreparedFunctionScope> {
    if functions.is_null() || num_functions == 0 {
        return None;
    }

    let mut scope_functions = Vec::new();
    let mut scope_provenance = std::collections::BTreeMap::new();
    for index in 0..num_functions {
        let function = unsafe { &*functions.add(index) };
        let provenance = scoped_function_provenance_from_ffi(function.provenance)?;
        let blocks = unsafe { BlockSlice::from_ffi(function.blocks, function.num_blocks) }?;
        let name = if function.name.is_null() {
            None
        } else {
            unsafe { CStr::from_ptr(function.name).to_str().ok() }.map(str::to_string)
        };
        let prepared = build_symbolic_prepared(blocks.as_slice(), arch, name.as_deref())?;
        scope_functions.push(r2sym::ScopedPreparedFunction {
            id: r2ssa::InterprocFunctionId(function.entry_addr),
            name,
            prepared,
        });
        scope_provenance.insert(r2ssa::InterprocFunctionId(function.entry_addr), provenance);
    }
    r2sym::PreparedFunctionScope::new_with_provenance(
        root_entry_addr,
        scope_functions,
        scope_provenance,
    )
}

#[cfg(test)]
mod tests {
    use super::{
        R2SLEIGH_SCOPED_FUNCTION_PROVENANCE_ANALYZED,
        R2SLEIGH_SCOPED_FUNCTION_PROVENANCE_RUNTIME_MATERIALIZED,
        scoped_function_provenance_from_ffi,
    };

    #[test]
    fn scoped_function_provenance_ffi_is_exact_and_name_independent() {
        assert_eq!(
            scoped_function_provenance_from_ffi(R2SLEIGH_SCOPED_FUNCTION_PROVENANCE_ANALYZED),
            Some(r2sym::sim::ScopedFunctionProvenance::Analyzed)
        );
        assert_eq!(
            scoped_function_provenance_from_ffi(
                R2SLEIGH_SCOPED_FUNCTION_PROVENANCE_RUNTIME_MATERIALIZED
            ),
            Some(r2sym::sim::ScopedFunctionProvenance::RuntimeMaterialized)
        );
        assert_eq!(scoped_function_provenance_from_ffi(2), None);
    }
}
