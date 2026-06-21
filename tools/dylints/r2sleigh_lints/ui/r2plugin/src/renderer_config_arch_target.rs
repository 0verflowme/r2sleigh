mod r2dec {
    pub struct DecompilerConfig;

    impl DecompilerConfig {
        pub fn for_arch<T>(_arch: T) -> Self {
            Self
        }

        pub fn for_arch_name(_arch_name: &str, _ptr_bits: u32) -> Self {
            Self
        }
    }
}

mod r2engine {
    pub fn engine_arch_target<T>(_arch: T) -> (&'static str, u32) {
        ("x86", 32)
    }
}

fn main() {
    let arch = ();
    let _ = r2dec::DecompilerConfig::for_arch(Some(&arch));

    let (arch_name, ptr_bits) = r2engine::engine_arch_target(Some(&arch));
    let _ = r2dec::DecompilerConfig::for_arch_name(arch_name, ptr_bits);
}
