use crate::R2ILContext;
use r2il::ArchSpec;
use r2sleigh_lift::Disassembler;

pub(crate) struct PluginCtxView<'a> {
    pub(crate) arch: Option<&'a ArchSpec>,
    pub(crate) disasm: &'a Disassembler,
}

pub(crate) fn require_ctx_view<'a>(ctx: *const R2ILContext) -> Option<PluginCtxView<'a>> {
    if ctx.is_null() {
        return None;
    }

    let ctx_ref = unsafe { &*ctx };
    let disasm = ctx_ref.disasm.as_ref()?;
    Some(PluginCtxView {
        arch: ctx_ref.arch.as_ref(),
        disasm,
    })
}
