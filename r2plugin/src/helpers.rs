use crate::ArchSpec;

pub(crate) fn effective_addr_size_bytes(arch: &ArchSpec) -> u32 {
    if arch.addr_size > 1 {
        return arch.addr_size;
    }

    if let Some(pc_size) = arch
        .registers
        .iter()
        .find(|reg| {
            matches!(
                reg.name.to_ascii_lowercase().as_str(),
                "pc" | "ip" | "eip" | "rip"
            )
        })
        .map(|reg| reg.size)
        .filter(|size| *size > 1)
    {
        return pc_size;
    }

    if let Some(default_size) = arch
        .spaces
        .iter()
        .find(|space| space.is_default && space.addr_size > 1)
        .map(|space| space.addr_size)
    {
        return default_size;
    }

    arch.spaces
        .iter()
        .map(|space| space.addr_size)
        .max()
        .filter(|size| *size > 1)
        .unwrap_or(arch.addr_size.max(1))
}

pub(crate) fn effective_ptr_bits(arch: &ArchSpec) -> u32 {
    effective_addr_size_bytes(arch).saturating_mul(8)
}
