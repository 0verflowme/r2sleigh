Symbolic Execution
==================

Background
----------

Symbolic execution explores program paths using symbolic values instead of
concrete data. When the executor reaches a branch condition that depends on
a symbolic value, it forks the state and explores both paths. A constraint
solver (Z3) determines which paths are feasible and can generate concrete
inputs that reach a target.

r2sleigh implements symbolic execution in the `r2sym` crate, operating on
SSA-form functions from `r2ssa`.

Key Types
---------

### SymValue

Represents a value during symbolic execution:

```rust
pub enum SymValue {
    Concrete(u64),      // Known constant
    Symbolic(BV<'ctx>), // Z3 bitvector expression
    Unknown,            // No information available
}
```

All symbolic values are Z3 bitvectors with explicit bit widths.

### SymState

The complete execution state at a point in the program:

- **Registers**: map from SSA variable name to `SymValue`
- **Memory**: symbolic memory model with concrete fallback
- **Constraints**: Z3 assertions accumulated along the path
- **Taint masks**: 64-bit mask per value, OR-propagated through operations
- **Program counter**: current execution address
- **Depth**: number of operations executed
- **Exit status**: how the state terminated (if finished)

### SymExecutor

Steps through SSA operations, updating state:

```rust
pub struct SymExecutor<'ctx> {
    ctx: &'ctx Context,
    call_hooks: HashMap<u64, CallHook<'ctx>>,
}
```

The executor:
1. Reads input SSA variables from the state
2. Computes the output using Z3 bitvector operations
3. Writes the result to the state
4. For branches, forks the state and adds path constraints

### Call Hooks

External function behavior can be modeled with call hooks:

```rust
executor.register_call_hook(printf_addr, |state| {
    // Model printf behavior
    Ok(CallHookResult::Fallthrough)
});
```

Hook results:
- `Fallthrough`: continue after the call
- `Jump(addr)`: redirect execution
- `Terminate(status)`: end the path

### Bitwidth Normalization

Mixed-width operations are handled by `normalize_widths()`, which zero-extends
the smaller operand to match the larger one before the Z3 operation.

Path Exploration
----------------

### ExploreConfig

```rust
pub struct ExploreConfig {
    pub max_states: usize,       // default: 1000
    pub max_depth: usize,        // default: 100
    pub timeout: Option<Duration>, // default: 60s
    pub strategy: ExploreStrategy, // DFS, BFS, or Random
    pub prune_infeasible: bool,  // default: true
    pub merge_states: bool,      // default: false
}
```

### Strategies

- **DFS** (default): depth-first, finds deep paths quickly
- **BFS**: breadth-first, explores shallow paths first
- **Random**: random path selection, good for coverage

### PathResult

```rust
pub struct PathResult<'ctx> {
    pub state: SymState<'ctx>,
    pub exit_status: ExitStatus,
    pub depth: usize,
    pub feasible: bool,
}
```

### SolvedPath

When Z3 finds a satisfying model, concrete values are extracted:

- **Inputs**: concrete register/memory values that reach the target
- **Final PC**: where execution ended
- **Constraints**: the path condition as Z3 assertions

Constraint Solving
------------------

The `SymSolver` wraps Z3 to check satisfiability and extract models:

```rust
let solver = SymSolver::new(&ctx);
let result = solver.check(&state.constraints);
match result {
    SolveResult::Sat(model) => {
        // Extract concrete input values from model
    }
    SolveResult::Unsat => { /* path is infeasible */ }
    SolveResult::Unknown => { /* solver timed out */ }
}
```

Memory Model
------------

`SymMemory` provides a flat symbolic memory with concrete fallback:

- Writes store `SymValue` at symbolic or concrete addresses
- Reads return `SymValue::Unknown` for uninitialized locations
- Concrete addresses can be pre-loaded from binary sections

Plugin Commands
---------------

Detached symbolic commands are unavailable. `a:sla.sym`, `a:sla.sym.paths`,
`a:sym.runj`, the `a:sym.explore*` and `a:sym.solve*` families, and commands
that build a detached symbolic scope cannot establish source authority from
live plugin state.

Symbolic execution requires a borrowed ABI-138/schema-9 function snapshot from
radare2's locked snapshot transaction. The snapshot is deep-copied
synchronously and then treated as immutable. Missing, stale, or incomplete
source authority is refused; there is no detached fallback or replacement
plugin API.
