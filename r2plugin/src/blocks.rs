use r2il::R2ILBlock;

pub(crate) struct BlockSlice {
    blocks: Vec<R2ILBlock>,
}

impl BlockSlice {
    pub(crate) unsafe fn from_ffi(
        blocks: *const *const R2ILBlock,
        len: usize,
    ) -> Option<BlockSlice> {
        if blocks.is_null() || len == 0 {
            return None;
        }

        let mut out = Vec::new();
        for idx in 0..len {
            let blk_ptr = unsafe { *blocks.add(idx) };
            if blk_ptr.is_null() {
                continue;
            }
            out.push(unsafe { (&*blk_ptr).clone() });
        }

        if out.is_empty() {
            None
        } else {
            Some(BlockSlice { blocks: out })
        }
    }

    pub(crate) fn as_slice(&self) -> &[R2ILBlock] {
        &self.blocks
    }
}
