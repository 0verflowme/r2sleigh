struct ControlFlowStructurer;

impl ControlFlowStructurer {
    fn switch_case_display_bias(&self) -> i64 {
        1
    }

    fn filter_switch_case_outliers(&self, cases: Vec<(u64, u64)>) -> Vec<(u64, u64)> {
        cases.into_iter().filter(|(value, _)| *value < 16).collect()
    }

    fn structure_switch_region(&self, case_value: u64) -> i64 {
        let display_bias = self.switch_case_display_bias();
        case_value.saturating_add_signed(display_bias) as i64
    }
}

fn main() {
    let structurer = ControlFlowStructurer;
    let _ = structurer.filter_switch_case_outliers(vec![(0, 0x1000), (408, 0x2000)]);
    let _ = structurer.structure_switch_region(0);
}
