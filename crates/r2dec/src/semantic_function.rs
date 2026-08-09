//! Fully authorized semantic-C functions for the currently admitted subset.

use std::fmt::Write as _;

use r2cert::CertifiedMachineProjection;
use r2ssa::{MachineBuildError, SsaArtifact};
use serde::Serialize;

use crate::certified_region::{CertifiedSingleBlockAccounting, RegionBuildError};
use crate::certified_return::{CertifiedTerminalReturnBlockRegion, TerminalReturnRegionError};
use crate::semantic_c::{
    SEMANTIC_C_HELPERS, SemanticCError, SemanticCFunctionReturn, SemanticCInputOrigin,
    storage_type, value_name,
};

pub const CERTIFIED_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedSemanticCFunctionScope {
    SingleTerminalReturnBlockWithoutMemory,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSemanticCFunction {
    schema_version: u32,
    scope: CertifiedSemanticCFunctionScope,
    name: String,
    region: CertifiedTerminalReturnBlockRegion,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CertifiedSemanticCFunctionError {
    Machine(MachineBuildError),
    Region(RegionBuildError),
    TerminalReturn(TerminalReturnRegionError),
    InvalidRegion(Vec<String>),
    InvalidRenderPermit,
    MissingFunctionInterface,
    MemoryRequiresSemanticRenderer,
    StackAddressRequiresMemoryRenderer,
    MissingReturnedEntity,
    SemanticC(SemanticCError),
}

impl std::fmt::Display for CertifiedSemanticCFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "certified semantic C function failed: {self:?}")
    }
}

impl std::error::Error for CertifiedSemanticCFunctionError {}

impl From<SemanticCError> for CertifiedSemanticCFunctionError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

impl From<MachineBuildError> for CertifiedSemanticCFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RegionBuildError> for CertifiedSemanticCFunctionError {
    fn from(error: RegionBuildError) -> Self {
        Self::Region(error)
    }
}

impl From<TerminalReturnRegionError> for CertifiedSemanticCFunctionError {
    fn from(error: TerminalReturnRegionError) -> Self {
        Self::TerminalReturn(error)
    }
}

impl CertifiedSemanticCFunction {
    /// Build the complete admitted authorization chain from one immutable SSA
    /// artifact. No child certificate or render token crosses this boundary.
    pub fn from_artifact(artifact: &SsaArtifact) -> Result<Self, CertifiedSemanticCFunctionError> {
        let certified = CertifiedMachineProjection::from_artifact(artifact)?;
        let accounting = CertifiedSingleBlockAccounting::from_projection(&certified)?;
        let region = CertifiedTerminalReturnBlockRegion::from_accounting(accounting)?;
        Self::from_terminal_region(region)
    }

    pub fn from_terminal_region(
        region: CertifiedTerminalReturnBlockRegion,
    ) -> Result<Self, CertifiedSemanticCFunctionError> {
        let report = region.audit();
        if !report.has_exact_terminal_return() {
            return Err(CertifiedSemanticCFunctionError::InvalidRegion(
                report.invalid().to_vec(),
            ));
        }
        if !region.render_permit().authorizes_certified_c() {
            return Err(CertifiedSemanticCFunctionError::InvalidRenderPermit);
        }
        let accounting = region.layer().accounting();
        if accounting.expression_layer().function_interface().is_none() {
            return Err(CertifiedSemanticCFunctionError::MissingFunctionInterface);
        }
        if !accounting.memory_statements().is_empty() {
            return Err(CertifiedSemanticCFunctionError::MemoryRequiresSemanticRenderer);
        }
        if accounting
            .expression_layer()
            .input_origins()
            .values()
            .any(|origin| matches!(origin, SemanticCInputOrigin::StackSlot { .. }))
        {
            return Err(CertifiedSemanticCFunctionError::StackAddressRequiresMemoryRenderer);
        }
        let returned = region
            .returned()
            .ok_or(CertifiedSemanticCFunctionError::MissingReturnedEntity)?;
        if let [value] = returned.values() {
            let return_position = region
                .layer()
                .steps()
                .iter()
                .position(|step| step.source() == region.return_producer())
                .ok_or(CertifiedSemanticCFunctionError::MissingReturnedEntity)?;
            let value_position = region
                .layer()
                .steps()
                .iter()
                .position(|step| {
                    step.value().is_some_and(|reference| {
                        region
                            .layer()
                            .resolve_value(reference)
                            .is_some_and(|entity| entity.output() == value.binding())
                    })
                })
                .ok_or(CertifiedSemanticCFunctionError::MissingReturnedEntity)?;
            if value_position >= return_position {
                return Err(CertifiedSemanticCFunctionError::MissingReturnedEntity);
            }
        }
        Ok(Self {
            schema_version: CERTIFIED_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope: CertifiedSemanticCFunctionScope::SingleTerminalReturnBlockWithoutMemory,
            name: format!("certified_sub_{:x}", accounting.block_addr()),
            region,
        })
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> CertifiedSemanticCFunctionScope {
        self.scope
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn region(&self) -> &CertifiedTerminalReturnBlockRegion {
        &self.region
    }

    /// Render the authorized unsigned-carrier C11 subset. Recovered source
    /// types and cosmetic names are deliberately not consulted.
    pub fn render_certified_c(&self) -> Result<String, CertifiedSemanticCFunctionError> {
        let report = self.region.audit();
        if self.schema_version != CERTIFIED_SEMANTIC_C_FUNCTION_SCHEMA_VERSION
            || self.scope != CertifiedSemanticCFunctionScope::SingleTerminalReturnBlockWithoutMemory
            || !report.has_exact_terminal_return()
            || !self.region.render_permit().authorizes_certified_c()
        {
            return Err(CertifiedSemanticCFunctionError::InvalidRegion(
                report.invalid().to_vec(),
            ));
        }
        let accounting = self.region.layer().accounting();
        let expressions = accounting.expression_layer();
        let interface = expressions
            .function_interface()
            .ok_or(CertifiedSemanticCFunctionError::MissingFunctionInterface)?;
        let return_type = match interface.return_kind() {
            SemanticCFunctionReturn::Void => "void",
            SemanticCFunctionReturn::Register { ty, .. } => storage_type(ty)?,
        };
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        output.push_str(SEMANTIC_C_HELPERS);
        write!(&mut output, "\n{return_type} {}(", self.name).expect("String writes cannot fail");
        if interface.parameters().is_empty() {
            output.push_str("void");
        } else {
            for (position, parameter) in interface.parameters().iter().enumerate() {
                if position > 0 {
                    output.push_str(", ");
                }
                let name = parameter
                    .value()
                    .map(value_name)
                    .unwrap_or_else(|| format!("arg_{}", parameter.index()));
                write!(&mut output, "{} {name}", storage_type(parameter.ty())?)
                    .expect("String writes cannot fail");
            }
        }
        output.push_str(") {\n");
        for parameter in interface.parameters() {
            let name = parameter
                .value()
                .map(value_name)
                .unwrap_or_else(|| format!("arg_{}", parameter.index()));
            writeln!(&mut output, "\t(void){name};").expect("String writes cannot fail");
        }
        for step in self.region.layer().steps() {
            let Some(reference) = step.value() else {
                continue;
            };
            let entity = self
                .region
                .layer()
                .resolve_value(reference)
                .ok_or(CertifiedSemanticCFunctionError::MissingReturnedEntity)?;
            let expression = expressions.render_expr(entity.root())?;
            writeln!(
                &mut output,
                "\t{} {} = {expression};",
                storage_type(expressions.expr_type(entity.root())?)?,
                value_name(entity.output())
            )
            .expect("String writes cannot fail");
        }
        let returned = self
            .region
            .returned()
            .ok_or(CertifiedSemanticCFunctionError::MissingReturnedEntity)?;
        match returned.values() {
            [] => output.push_str("\treturn;\n"),
            [value] => writeln!(&mut output, "\treturn {};", value_name(value.binding()))
                .expect("String writes cannot fail"),
            _ => return Err(CertifiedSemanticCFunctionError::MissingReturnedEntity),
        }
        output.push_str("}\n");
        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    use r2il::{ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceFunctionInterface,
        SourceFunctionReturn, SourceStackSlotSpec, SsaArtifact, StackAddressBase,
    };

    fn test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("semantic-function-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(Endianness::Little);
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rip", 16, 8));
        arch.add_register(RegisterDef::new("rsp", 24, 8));
        arch
    }

    fn register_storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn source_interface(
        return_kind: SourceFunctionReturn,
        stack_slots: impl IntoIterator<Item = SourceStackSlotSpec>,
    ) -> SourceFunctionInterface {
        SourceFunctionInterface::new(
            b"semantic-function-revision-1".to_vec(),
            "test-register-abi",
            [SourceAbiParameterSpec::new(0, register_storage(8))],
            return_kind,
            stack_slots,
        )
        .expect("explicit interface")
    }

    fn assert_public_constructor_refuses(artifact: &SsaArtifact) {
        if let Ok(function) = CertifiedSemanticCFunction::from_artifact(artifact) {
            let authorized = function.region().render_permit().authorizes_certified_c();
            let rendered = function.render_certified_c();
            panic!(
                "excluded shape produced semantic function: authorized={authorized}, rendered={rendered:?}"
            );
        }
    }

    fn function(return_kind: SourceFunctionReturn) -> CertifiedSemanticCFunction {
        let mut block = R2ILBlock::new(0x7200, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(8, 8),
            b: Varnode::constant(1, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::unique(0x10, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let arch = test_arch();
        let interface = source_interface(return_kind, []);
        let artifact = SsaArtifact::raw_with_interface(&[block], Some(&arch), interface)
            .expect("semantic function artifact");
        CertifiedSemanticCFunction::from_artifact(&artifact).expect("semantic C function")
    }

    fn compile(source: &str) {
        let mut compiler = Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Wpedantic",
                "-Wno-unused-function",
                "-Werror",
                "-fsyntax-only",
                "-x",
                "c",
                "-",
            ])
            .stdin(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("C compiler required");
        compiler
            .stdin
            .as_mut()
            .expect("compiler stdin")
            .write_all(source.as_bytes())
            .expect("write C source");
        let output = compiler.wait_with_output().expect("wait for compiler");
        assert!(
            output.status.success(),
            "generated C failed:\n{}\n{}",
            source,
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn register_return_function_has_final_r2cert_permit_and_compiles_as_c11() {
        let function = function(SourceFunctionReturn::Register {
            storage: CanonicalStorageId {
                space: CanonicalStorageSpace::Register,
                offset: 0,
                size: 8,
            },
        });
        assert!(function.region().render_permit().authorizes_certified_c());
        let source = function.render_certified_c().expect("certified C");
        assert!(source.contains("uint64_t certified_sub_7200(uint64_t v_"));
        assert!(source.contains("return v_"));
        compile(&source);
    }

    #[test]
    fn explicit_void_function_is_distinct_and_compiles() {
        let function = function(SourceFunctionReturn::Void);
        let source = function.render_certified_c().expect("certified void C");
        assert!(source.contains("void certified_sub_7200(uint64_t v_"));
        assert!(source.contains("\treturn;"));
        compile(&source);
    }

    #[test]
    fn public_constructor_refuses_missing_source_function_interface() {
        let mut block = R2ILBlock::new(0x7240, 4);
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let arch = test_arch();
        let artifact = SsaArtifact::raw(&[block], Some(&arch)).expect("interface-free artifact");

        assert_public_constructor_refuses(&artifact);
    }

    #[test]
    fn public_constructor_refuses_memory_statement() {
        let mut block = R2ILBlock::new(0x7280, 4);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x1000, 8),
            val: Varnode::constant(0x2a, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let arch = test_arch();
        let interface = source_interface(SourceFunctionReturn::Void, []);
        let artifact = SsaArtifact::raw_with_interface(&[block], Some(&arch), interface)
            .expect("memory artifact");

        assert_public_constructor_refuses(&artifact);
    }

    #[test]
    fn public_constructor_refuses_stack_address_input() {
        let mut block = R2ILBlock::new(0x72c0, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(24, 8),
            b: Varnode::constant(0, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::unique(0x10, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let arch = test_arch();
        let interface = source_interface(
            SourceFunctionReturn::Register {
                storage: register_storage(0),
            },
            [SourceStackSlotSpec::new(
                StackAddressBase::StackPointer,
                register_storage(24),
                0,
                8,
            )],
        );
        let artifact = SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("stack-address artifact");

        assert_public_constructor_refuses(&artifact);
    }

    #[test]
    fn public_constructor_refuses_direct_call() {
        let mut block = R2ILBlock::new(0x7300, 4);
        block.push(R2ILOp::Call {
            target: Varnode::ram(0x8000, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let arch = test_arch();
        let interface = source_interface(SourceFunctionReturn::Void, []);
        let artifact = SsaArtifact::raw_with_interface(&[block], Some(&arch), interface)
            .expect("direct-call artifact");

        assert_public_constructor_refuses(&artifact);
    }

    #[test]
    fn public_constructor_refuses_multiple_blocks() {
        let mut entry = R2ILBlock::new(0x7340, 4);
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x7350, 8),
        });
        let mut returned = R2ILBlock::new(0x7350, 4);
        returned.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let arch = test_arch();
        let interface = source_interface(SourceFunctionReturn::Void, []);
        let artifact = SsaArtifact::raw_with_interface(&[entry, returned], Some(&arch), interface)
            .expect("multi-block artifact");

        assert_public_constructor_refuses(&artifact);
    }

    #[test]
    fn public_constructor_refuses_ungrounded_register_return_shape() {
        let mut block = R2ILBlock::new(0x7380, 4);
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let arch = test_arch();
        let interface = source_interface(
            SourceFunctionReturn::Register {
                storage: register_storage(0),
            },
            [],
        );
        let artifact = SsaArtifact::raw_with_interface(&[block], Some(&arch), interface)
            .expect("ungrounded return artifact");

        assert_public_constructor_refuses(&artifact);
    }
}
