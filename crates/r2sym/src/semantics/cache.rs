use r2ssa::{SSA_SEMANTIC_FINGERPRINT_SCHEMA_VERSION, stable_ssa_semantic_fingerprint};

use crate::sim::{PreparedFunctionScope, ScopedFunctionProvenance};

pub const SEMANTIC_ARTIFACT_SCHEMA_VERSION: u32 = 13;

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

struct ScopeFingerprint(u64);

impl ScopeFingerprint {
    fn new() -> Self {
        Self(FNV_OFFSET)
    }

    fn bytes(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(FNV_PRIME);
        }
    }

    fn u8(&mut self, value: u8) {
        self.bytes(&[value]);
    }

    fn u32(&mut self, value: u32) {
        self.bytes(&value.to_le_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.bytes(&value.to_le_bytes());
    }

    fn string(&mut self, value: &str) {
        self.u64(value.len() as u64);
        self.bytes(value.as_bytes());
    }

    fn finish(self) -> u64 {
        self.0
    }
}

fn provenance_tag(provenance: Option<ScopedFunctionProvenance>) -> u8 {
    match provenance {
        Some(ScopedFunctionProvenance::Analyzed) => 1,
        Some(ScopedFunctionProvenance::RuntimeMaterialized) => 2,
        None => 0,
    }
}

pub fn stable_scope_hash(scope: Option<&PreparedFunctionScope>) -> u64 {
    let Some(scope) = scope else {
        return 0;
    };
    let mut fingerprint = ScopeFingerprint::new();
    fingerprint.string("r2sym-prepared-function-scope-v2");
    fingerprint.u64(scope.root_id().0);
    fingerprint.u64(scope.functions().len() as u64);
    for function in scope.functions().values() {
        fingerprint.u64(function.id.0);
        fingerprint.u8(provenance_tag(scope.provenance_of(function)));
        fingerprint.u32(SSA_SEMANTIC_FINGERPRINT_SCHEMA_VERSION);
        fingerprint.u64(stable_ssa_semantic_fingerprint(&function.prepared));
    }
    fingerprint.finish()
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use r2il::{
        ArchSpec, MemoryOrdering, R2ILBlock, R2ILOp, RegisterDef, SpaceId, SwitchCase, SwitchInfo,
        Varnode,
    };
    use r2ssa::{InterprocFunctionId, SsaArtifact};

    use crate::sim::{PreparedFunctionScope, ScopedFunctionProvenance, ScopedPreparedFunction};

    use super::stable_scope_hash;

    fn make_const(value: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: value,
            size,
            meta: None,
        }
    }

    fn make_register(offset: u64) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
            size: 8,
            meta: None,
        }
    }

    fn make_unique(offset: u64) -> Varnode {
        Varnode {
            space: SpaceId::Unique,
            offset,
            size: 8,
            meta: None,
        }
    }

    fn make_leaf(entry: u64) -> SsaArtifact {
        make_leaf_value(entry, 0)
    }

    fn make_leaf_value(entry: u64, value: u64) -> SsaArtifact {
        SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr: entry,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(value, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            None,
        )
        .expect("ssa")
    }

    fn single_function_scope(name: &str, prepared: SsaArtifact) -> PreparedFunctionScope {
        let id = InterprocFunctionId(prepared.function().entry);
        PreparedFunctionScope::new(
            id.0,
            vec![ScopedPreparedFunction {
                id,
                name: Some(name.to_string()),
                prepared: prepared.with_name(name),
            }],
        )
        .expect("scope")
    }

    fn diamond_blocks(left_value: u64, right_value: u64) -> Vec<R2ILBlock> {
        vec![
            R2ILBlock {
                addr: 0x3000,
                size: 1,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x3010, 8),
                    cond: make_register(0),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x3001,
                size: 1,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_register(8),
                        src: make_const(left_value, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x3020, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x3010,
                size: 1,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_register(8),
                        src: make_const(right_value, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x3020, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x3020,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_register(8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ]
    }

    fn renamed_arch(condition: &str, result: &str) -> ArchSpec {
        let mut arch = ArchSpec::new("scope-fingerprint-test");
        arch.add_register(RegisterDef::new(condition, 0, 8));
        arch.add_register(RegisterDef::new(result, 8, 8));
        arch
    }

    fn payload_scope(ordering: MemoryOrdering, userop: u32) -> PreparedFunctionScope {
        let prepared = SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr: 0x4000,
                size: 1,
                ops: vec![
                    R2ILOp::Fence { ordering },
                    R2ILOp::CallOther {
                        output: Some(make_unique(0)),
                        userop,
                        inputs: vec![make_const(7, 8)],
                    },
                    R2ILOp::Return {
                        target: make_unique(0),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            None,
        )
        .expect("payload SSA");
        single_function_scope("payload", prepared)
    }

    fn switch_scope(second_target: u64) -> PreparedFunctionScope {
        let mut blocks = vec![R2ILBlock {
            addr: 0x5000,
            size: 1,
            ops: vec![R2ILOp::BranchInd {
                target: make_register(0),
            }],
            switch_info: Some(SwitchInfo {
                switch_addr: 0x5000,
                min_val: 0,
                max_val: 1,
                default_target: Some(0x5030),
                cases: vec![
                    SwitchCase {
                        value: 0,
                        target: 0x5010,
                    },
                    SwitchCase {
                        value: 1,
                        target: second_target,
                    },
                ],
            }),
            op_metadata: Default::default(),
        }];
        for addr in [0x5010, 0x5020, 0x5030] {
            blocks.push(R2ILBlock {
                addr,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(addr, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            });
        }
        single_function_scope(
            "switch",
            SsaArtifact::for_symbolic(&blocks, None).expect("switch SSA"),
        )
    }

    fn make_scope(
        root_name: &str,
        helper_name: &str,
        helper_provenance: ScopedFunctionProvenance,
    ) -> PreparedFunctionScope {
        let root_id = InterprocFunctionId(0x1000);
        let helper_id = InterprocFunctionId(0x2000);
        PreparedFunctionScope::new_with_provenance(
            root_id.0,
            vec![
                ScopedPreparedFunction {
                    id: root_id,
                    name: Some(root_name.to_string()),
                    prepared: make_leaf(root_id.0).with_name(root_name),
                },
                ScopedPreparedFunction {
                    id: helper_id,
                    name: Some(helper_name.to_string()),
                    prepared: make_leaf(helper_id.0).with_name(helper_name),
                },
            ],
            BTreeMap::from([
                (root_id, ScopedFunctionProvenance::Analyzed),
                (helper_id, helper_provenance),
            ]),
        )
        .expect("scope")
    }

    #[test]
    fn stable_scope_hash_ignores_display_names_but_binds_provenance() {
        let named = make_scope(
            "sym.worker",
            "sym.helper",
            ScopedFunctionProvenance::Analyzed,
        );
        let renamed = make_scope("dbg.worker", "fcn.2000", ScopedFunctionProvenance::Analyzed);
        let materialized = make_scope(
            "dbg.worker",
            "fcn.2000",
            ScopedFunctionProvenance::RuntimeMaterialized,
        );

        assert_eq!(
            stable_scope_hash(Some(&named)),
            stable_scope_hash(Some(&renamed))
        );
        assert_ne!(
            stable_scope_hash(Some(&named)),
            stable_scope_hash(Some(&materialized))
        );
    }

    #[test]
    fn stable_scope_hash_ignores_ssa_names_and_input_block_order() {
        let blocks = diamond_blocks(1, 2);
        let first = SsaArtifact::for_symbolic(&blocks, Some(&renamed_arch("condition", "result")))
            .expect("first SSA");
        let reordered = vec![
            blocks[0].clone(),
            blocks[2].clone(),
            blocks[1].clone(),
            blocks[3].clone(),
        ];
        let second = SsaArtifact::for_symbolic(
            &reordered,
            Some(&renamed_arch("renamed_condition", "renamed_result")),
        )
        .expect("renamed SSA");
        assert_eq!(
            stable_scope_hash(Some(&single_function_scope("first", first))),
            stable_scope_hash(Some(&single_function_scope("second", second)))
        );
    }

    #[test]
    fn stable_scope_hash_binds_constants_and_phi_predecessor_values() {
        let constant_a = single_function_scope("leaf", make_leaf_value(0x6000, 1));
        let constant_b = single_function_scope("leaf", make_leaf_value(0x6000, 2));
        assert_ne!(
            stable_scope_hash(Some(&constant_a)),
            stable_scope_hash(Some(&constant_b))
        );

        let first = single_function_scope(
            "diamond",
            SsaArtifact::for_symbolic(&diamond_blocks(1, 2), None).expect("first diamond"),
        );
        let swapped = single_function_scope(
            "diamond",
            SsaArtifact::for_symbolic(&diamond_blocks(2, 1), None).expect("swapped diamond"),
        );
        assert_ne!(
            stable_scope_hash(Some(&first)),
            stable_scope_hash(Some(&swapped))
        );
    }

    #[test]
    fn stable_scope_hash_binds_switch_ordering_and_userop_semantics() {
        assert_ne!(
            stable_scope_hash(Some(&switch_scope(0x5020))),
            stable_scope_hash(Some(&switch_scope(0x5030)))
        );
        assert_ne!(
            stable_scope_hash(Some(&payload_scope(MemoryOrdering::Acquire, 7))),
            stable_scope_hash(Some(&payload_scope(MemoryOrdering::SeqCst, 7)))
        );
        assert_ne!(
            stable_scope_hash(Some(&payload_scope(MemoryOrdering::Acquire, 7))),
            stable_scope_hash(Some(&payload_scope(MemoryOrdering::Acquire, 8)))
        );
    }
}
