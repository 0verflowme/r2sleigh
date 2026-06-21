struct Structurer;

impl Structurer {
    fn structure_semantic_worker_islands(&mut self, _: usize) -> Option<()> {
        Some(())
    }
}

fn semantic_worker_structured_body(_: &str, _: ()) {}

fn unrelated_debug_probe(structurer: &mut Structurer) {
    if let Some(structured) = structurer.structure_semantic_worker_islands(1) {
        semantic_worker_structured_body("debug-only probe", structured);
    }
}

fn main() {
    let mut structurer = Structurer;
    unrelated_debug_probe(&mut structurer);
}
