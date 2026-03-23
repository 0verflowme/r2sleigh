use r2il::{R2ILBlock, R2ILOp, SpaceId, Varnode};
use r2ssa::PreparedFunctionSSA;
use r2sym::{ExploreConfig, PathExplorer, SymState};
use z3::Context;

const ENTRY: u64 = 0x1000;
const FAIL: u64 = 0x1004;
const SUCCESS: u64 = 0x1020;
const INPUT_ADDR: u64 = 0x2000;

fn main() {
    // C-like logic modeled by the r2il blocks below:
    //
    // int check(const unsigned char *buf) {
    //   if (buf[0]=='A' && buf[1]=='I' && buf[2]=='S' && buf[3]=='3') return 1;
    //   return 0;
    // }
    //
    // This example solves for the 4-byte input using r2sym.

    let blocks = build_blocks();
    let func = PreparedFunctionSSA::for_symbolic(&blocks, None).expect("SSA build failed");

    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, ENTRY);
    state.make_symbolic_memory(INPUT_ADDR, 4, "input");

    let config = ExploreConfig {
        max_states: 16,
        max_depth: 32,
        timeout: None,
        ..Default::default()
    };

    let mut explorer = PathExplorer::with_config(&ctx, config);
    let results = explorer.explore(&func, state);

    let success = results
        .iter()
        .find(|path| path.feasible && path.final_pc() == SUCCESS)
        .expect("no satisfying path");

    let solved = explorer
        .solve_path(success)
        .expect("no model for success path");
    let bytes = solved.memory.get("input").expect("missing input buffer");

    let printable = String::from_utf8_lossy(bytes);
    println!("input bytes: {:02x?}", bytes);
    println!("input string: {}", printable);
}

fn build_blocks() -> Vec<R2ILBlock> {
    let mut blocks = Vec::new();

    let mut entry = R2ILBlock::new(ENTRY, 4);

    let addr0 = Varnode::constant(INPUT_ADDR, 8);
    let addr1 = Varnode::constant(INPUT_ADDR + 1, 8);
    let addr2 = Varnode::constant(INPUT_ADDR + 2, 8);
    let addr3 = Varnode::constant(INPUT_ADDR + 3, 8);

    let b0 = Varnode::unique(0x10, 1);
    let b1 = Varnode::unique(0x11, 1);
    let b2 = Varnode::unique(0x12, 1);
    let b3 = Varnode::unique(0x13, 1);

    let eq0 = Varnode::unique(0x20, 1);
    let eq1 = Varnode::unique(0x21, 1);
    let eq2 = Varnode::unique(0x22, 1);
    let eq3 = Varnode::unique(0x23, 1);

    let and01 = Varnode::unique(0x30, 1);
    let and012 = Varnode::unique(0x31, 1);
    let cond = Varnode::unique(0x32, 1);

    entry.push(R2ILOp::Load {
        dst: b0.clone(),
        addr: addr0,
        space: SpaceId::Ram,
    });
    entry.push(R2ILOp::IntEqual {
        dst: eq0.clone(),
        a: b0,
        b: Varnode::constant(b'A' as u64, 1),
    });

    entry.push(R2ILOp::Load {
        dst: b1.clone(),
        addr: addr1,
        space: SpaceId::Ram,
    });
    entry.push(R2ILOp::IntEqual {
        dst: eq1.clone(),
        a: b1,
        b: Varnode::constant(b'I' as u64, 1),
    });
    entry.push(R2ILOp::BoolAnd {
        dst: and01.clone(),
        a: eq0,
        b: eq1,
    });

    entry.push(R2ILOp::Load {
        dst: b2.clone(),
        addr: addr2,
        space: SpaceId::Ram,
    });
    entry.push(R2ILOp::IntEqual {
        dst: eq2.clone(),
        a: b2,
        b: Varnode::constant(b'S' as u64, 1),
    });
    entry.push(R2ILOp::BoolAnd {
        dst: and012.clone(),
        a: and01,
        b: eq2,
    });

    entry.push(R2ILOp::Load {
        dst: b3.clone(),
        addr: addr3,
        space: SpaceId::Ram,
    });
    entry.push(R2ILOp::IntEqual {
        dst: eq3.clone(),
        a: b3,
        b: Varnode::constant(b'3' as u64, 1),
    });
    entry.push(R2ILOp::BoolAnd {
        dst: cond.clone(),
        a: and012,
        b: eq3,
    });

    entry.push(R2ILOp::CBranch {
        target: Varnode::constant(SUCCESS, 8),
        cond,
    });

    blocks.push(entry);

    let mut fail = R2ILBlock::new(FAIL, 4);
    fail.push(R2ILOp::Copy {
        dst: Varnode::register(0, 8),
        src: Varnode::constant(0, 8),
    });
    fail.push(R2ILOp::Return {
        target: Varnode::constant(0, 8),
    });
    blocks.push(fail);

    let mut success = R2ILBlock::new(SUCCESS, 4);
    success.push(R2ILOp::Copy {
        dst: Varnode::register(0, 8),
        src: Varnode::constant(1, 8),
    });
    success.push(R2ILOp::Return {
        target: Varnode::constant(0, 8),
    });
    blocks.push(success);

    blocks
}
