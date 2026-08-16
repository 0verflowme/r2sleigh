mod r2types {
    pub fn build_source_owned_type_writeback_analysis() {}
}

fn main() {
    r2types::build_source_owned_type_writeback_analysis();
}

mod tests {
    #[test]
    fn tests_may_exercise_the_low_level_owner_boundary() {
        super::r2types::build_source_owned_type_writeback_analysis();
    }
}
