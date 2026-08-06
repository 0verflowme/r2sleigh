mod r2dec {
    pub struct VariableRecovery;

    impl VariableRecovery {
        pub fn new(_sp: &str, _fp: &str, _ptr_size: u32) -> Self {
            Self
        }

        pub fn new_with_abi(
            _sp: &str,
            _fp: &str,
            _ptr_size: u32,
            _arg_regs: Vec<String>,
            _ret_regs: Vec<String>,
        ) -> Self {
            Self
        }
    }
}

fn main() {
    let _ = r2dec::VariableRecovery::new("rsp", "rbp", 8);
    let _ = r2dec::VariableRecovery::new_with_abi("rsp", "rbp", 8, Vec::new(), Vec::new());
}
