r2dec -- Decompiler
===================

Background
----------

The r2dec decompiler converts SSA-form functions into readable C code. It
operates as a pipeline of transformations: expression folding, control flow
structuring, symbol resolution, and code generation.

The production decompiler is invoked through radare2's `pdd` provider after
`a:sla` loads the Sleigh architecture. Programmatic certified rendering accepts
only an opaque trusted SSA artifact derived from the same source snapshot.

Pipeline Overview
-----------------

```
SSAFunction
    |
    v
FoldingContext (fold.rs)
    - Use counting
    - Single-use inlining
    - Dead code elimination
    - Constant folding
    - Predicate simplification
    - Identity elimination
    |
    v
RegionAnalyzer (region.rs)
    - Identify control flow regions
    - Detect loops, conditionals, switches
    |
    v
ControlFlowStructurer (structure.rs)
    - Convert regions to CStmt/CExpr AST
    - For-loop detection
    - Switch detection
    |
    v
CodeGenerator (codegen.rs)
    - Pretty-print AST to C string
    - Operator precedence
    - Indentation and formatting
    |
    v
C code string
```

Expression Folding (fold.rs)
----------------------------

`FoldingContext` is the central optimization engine. It performs multiple
passes over the SSA blocks:

### Use Counting

Each SSA variable is counted for how many times it appears as an input. This
determines what can be inlined and what is dead code.

### Single-Use Inlining

Variables used exactly once are inlined at the use site. This eliminates
most temporaries:

```
// Before:
tmp_1 = rbp - 8
rax_1 = *[ram] tmp_1

// After inlining:
rax_1 = *(rbp - 8)
```

### Dead Code Elimination

CPU flags that are computed but never read in a branch condition are removed.
The following flags are auto-eliminated when unused:

- `cf`, `pf`, `af`, `zf`, `sf`, `of`, `df`, `tf`
- Versioned variants: `cf_1`, `zf_2`, etc.

Dead temporary assignments (where the destination is never used) are also
pruned.

### Constant Folding

`const:xxx` SSA variables are converted to numeric literals:

- `const:0x42` becomes `0x42`
- `const:fffffffc` becomes `0xfffffffcU`

### Arithmetic Identity Elimination

Trivial operations are simplified:

| Pattern | Result |
|---------|--------|
| `x + 0` | `x` |
| `x - 0` | `x` |
| `x * 1` | `x` |
| `x \| 0` | `x` |
| `x & 0xffffffff` (when x is 32-bit) | `x` |

### Predicate Simplification

x86 comparisons are encoded as flag computations. The decompiler reconstructs
high-level comparisons:

| Flag Pattern | Reconstructed | Meaning |
|-------------|---------------|---------|
| `ZF` | `a == b` | Equal |
| `!ZF` | `a != b` | Not equal |
| `CF` | `a < b` | Unsigned less than |
| `!CF && !ZF` | `a > b` | Unsigned greater than |
| `OF == SF` | `a >= b` | Signed greater or equal |
| `!ZF && OF == SF` | `a > b` | Signed greater than |
| `OF != SF` | `a < b` | Signed less than |

The simplifier also handles:
- `!(x == 0)` becomes `x != 0`
- `BoolXor`/`BoolAnd`/`BoolOr` reconstruction
- Transitive flag-only elimination (flag temporaries consumed only by other
  flag ops)

### Flag-Only Temp Elimination

If a temporary variable is consumed exclusively by flag operations (which
themselves are dead), the temporary and all its consumers are removed together.

Control Flow Structuring
------------------------

### Region Analysis (region.rs)

The region analyzer identifies structured control flow patterns in the CFG:

| Region | C Output |
|--------|----------|
| `Block` | Statement sequence |
| `IfThenElse` | `if (cond) { ... } else { ... }` |
| `WhileLoop` | `while (cond) { ... }` |
| `DoWhileLoop` | `do { ... } while (cond);` |
| `Switch` | `switch (var) { case N: ... }` |
| `Irreducible` | Labels + gotos (fallback) |

### For-Loop Detection

The structurer detects the pattern `init; while(cond) { body; update }` and
converts it to `for(init; cond; update) { body }`.

Detection criteria:
1. A single initialization statement before the loop
2. A loop condition test
3. An update statement at the end of the loop body
4. The update modifies the same variable tested in the condition

### Switch Detection

Cascaded `if-else` chains testing the same variable against different
constants are converted to `switch` statements:

```c
// Before:
if (x == 1) { ... }
else if (x == 2) { ... }
else if (x == 3) { ... }
else { ... }

// After:
switch (x) {
    case 1: ...; break;
    case 2: ...; break;
    case 3: ...; break;
    default: ...;
}
```

### Safety Budget

Each block's control-domain proof has its own budget. The proof first removes
predicates from completed inner loops and takes the reverse CFG slice that can
reach the block. For `p` remaining Boolean predicates and `f` source/rendered
formula slots, its BDD may allocate at most `2^p * f` nodes: the size of the
explicit assignment table the BDD replaces, saturated to the addressable node
count. The proof refuses if that exact block-local bound is exhausted.

C AST Types (ast.rs)
--------------------

### CExpr -- Expressions

```rust
pub enum CExpr {
    IntLit(i64),
    UIntLit(u64),
    StringLit(String),
    Var(String),
    Binary { op: BinaryOp, left: Box<CExpr>, right: Box<CExpr> },
    Unary { op: UnaryOp, operand: Box<CExpr> },
    Call { func: Box<CExpr>, args: Vec<CExpr> },
    Deref(Box<CExpr>),
    Member { expr: Box<CExpr>, field: String },
    PtrMember { expr: Box<CExpr>, field: String },
    Cast { ty: CType, expr: Box<CExpr> },
    Subscript { base: Box<CExpr>, index: Box<CExpr> },
    // ...
}
```

### CStmt -- Statements

```rust
pub enum CStmt {
    Expr(CExpr),
    Assign { lhs: CExpr, rhs: CExpr },
    If { cond: CExpr, then_body: Box<CStmt>, else_body: Option<Box<CStmt>> },
    While { cond: CExpr, body: Box<CStmt> },
    DoWhile { body: Box<CStmt>, cond: CExpr },
    For { init: Box<CStmt>, cond: CExpr, update: Box<CStmt>, body: Box<CStmt> },
    Switch { expr: CExpr, cases: Vec<(i64, CStmt)>, default: Option<Box<CStmt>> },
    Block(Vec<CStmt>),
    Return(Option<CExpr>),
    Break,
    Continue,
    Label(String),
    Goto(String),
    // ...
}
```

### CFunction

```rust
pub struct CFunction {
    pub name: String,
    pub params: Vec<(CType, String)>,
    pub ret_type: CType,
    pub locals: Vec<(CType, String)>,
    pub body: CStmt,
}
```

Symbol Resolution
-----------------

The decompiler resolves addresses to human-readable symbols using data from
radare2:

### Function Names

`call(0x401234)` becomes `printf(...)` by looking up the function name at the
call target address (via `aflj` in radare2).

### String Literals

`printf(0x403008)` becomes `printf("Usage: %s\n")` when the address points to
a null-terminated string in `.rodata`. Strings are properly C-escaped:
`\n`, `\t`, `\"`, `\\`, `\xNN`.

### Global Symbols

`ram:0x404040` becomes `obj.global_counter` using radare2 flags.

### Stack Variables

`*(rbp - 0x70)` becomes `local_70` using radare2's `afvj` (variable list) or
automatic stack offset naming.

### Function Signatures

Parameter types and names are read from `afcfj` (function call format JSON).
This provides correct parameter names and types for known library functions.

Three-Tier Fallback
-------------------

For robustness with complex or unusual functions, the decompiler has three
tiers:

1. **Folded structuring** (primary): Full expression folding + control flow
   structuring. Produces the best output.

2. **Unfolded structuring**: Minimal folding, more conservative structuring.
   Used when folding causes issues (e.g., undeclared variables).

3. **Linear emission**: Per-block sequential statement output. Last resort
   for very complex or pathological CFGs.

When fallback triggers, the output includes a diagnostic comment:

```c
/* r2dec fallback: exceeded safety budget */
void function_name() {
    // ... simplified output ...
}
```

Code Generation (codegen.rs)
-----------------------------

`CodeGenerator` converts the C AST to a formatted string with:

- Proper operator precedence (avoiding unnecessary parentheses)
- Configurable indentation (default: 4 spaces)
- C99 fixed-width types (`uint32_t`, `int64_t`, etc.)
- String literal escaping
- For-loop formatting

### Configuration

```rust
pub struct CodeGenConfig {
    pub indent: usize,        // spaces per indent level
    pub use_c99_types: bool,  // uint32_t vs unsigned int
}
```

Type Inference Integration
--------------------------

The decompiler integrates with `r2types` for type information:

- Pointer types inferred from Load/Store address usage
- Signedness from IntSLess/IntSDiv/IntSRight (signed) vs IntLess/IntDiv/IntRight (unsigned)
- Function signatures from the signature registry
- Size-based fallback (4 bytes = `int`, 8 bytes = `long`)

See [types.md](types.md) for the full type inference documentation.

Plugin Command
--------------

| Command | Output | Description |
|---------|--------|-------------|
| `pdd` | C code or an explicit residual/refusal | Decompile the function from a bounded borrowed snapshot |

Example:

```bash
r2 -qc 'a:sla; aaa; s main; pdd' /bin/ls
```
