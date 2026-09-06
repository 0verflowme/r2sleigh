r2il -- Intermediate Language
=============================

Background
----------

Binary analysis tools traditionally use string-based intermediate
representations like radare2's ESIL. ESIL is compact and evaluable, but it
lacks type information, has no concept of address spaces, and encodes
everything as stack operations on opaque strings. This makes precise dataflow
analysis difficult.

r2il is a strongly-typed intermediate language based on Ghidra's P-code
operations. Every operation has explicit input and output varnodes with known
sizes and address spaces. This makes it suitable for SSA transformation,
symbolic execution, type inference, and decompilation -- while still being
convertible back to ESIL for backward compatibility with radare2.

### Comparison to Other ILs

| Aspect | r2il | P-code (Ghidra) | RzIL (rizin) | ESIL (radare2) |
|--------|------|-----------------|--------------|----------------|
| Typing | Sized varnodes | Sized varnodes | Typed (bitvectors, booleans) | Untyped strings |
| Address spaces | Yes (5 kinds) | Yes | Yes (variables + memory) | No |
| Serializable | Yes (serde/postcard) | Binary format | In-memory only | String |
| SSA-ready | Yes | No | No | No |
| Executable | Via r2sym | Via Ghidra emulator | Via RzIL VM | Via ESIL VM |
| Source | Sleigh specifications | Sleigh specifications | Hand-written per arch | Hand-written per arch |

r2il is intentionally close to P-code. Every Ghidra P-code opcode has a
direct r2il equivalent. The main differences are:

1. r2il uses Rust enums with named fields instead of generic instruction
   structs
2. Address spaces are an enum (`SpaceId`) rather than integer indices
3. Varnodes carry their space inline rather than referencing by index

Address Spaces (SpaceId)
------------------------

Every piece of data in r2il lives in an address space:

```rust
pub enum SpaceId {
    Ram,         // Main memory
    Register,    // CPU registers
    Unique,      // Temporaries (intermediate values within one instruction)
    Const,       // Immediate/literal values
    Custom(u32), // Architecture-specific spaces
}
```

| Space | Description | Example |
|-------|-------------|---------|
| Ram | Main memory addresses | `Ram:0x404000[4]` -- 4 bytes at 0x404000 |
| Register | Processor registers by offset | `Register:0x00[8]` -- RAX on x86-64 |
| Unique | Temporaries for complex instructions | `Unique:0x1000[8]` -- intermediate result |
| Const | Literal values (offset IS the value) | `Const:0x2a[4]` -- the integer 42 |
| Custom(n) | Architecture-specific (rare) | Used by some Sleigh specs |

Registers are addressed by offset within the register space. The mapping from
offset to register name (e.g., offset 0x00 = RAX, offset 0x20 = RSP on
x86-64) comes from the Sleigh processor specification.

Varnode
-------

A `Varnode` is the fundamental unit of data -- a sized location in an address
space:

```rust
pub struct Varnode {
    pub space: SpaceId,  // Where the data lives
    pub offset: u64,     // Location within the space
    pub size: u32,       // Size in bytes
    pub meta: Option<VarnodeMetadata>, // Optional advisory hints
}
```

### Construction

```rust
Varnode::constant(42, 4)          // 4-byte literal value 42
Varnode::register(0x00, 8)        // 8-byte register at offset 0 (RAX on x86-64)
Varnode::ram(0x404000, 4)         // 4-byte memory location
Varnode::unique(0x1000, 8)        // 8-byte temporary
```

### Display Format

```
0x2a:4                  -- constant 42, 4 bytes
reg:0x0[8]              -- register at offset 0, 8 bytes
ram:0x404000[4]         -- RAM at 0x404000, 4 bytes
uniq:0x1000[8]          -- temporary 0x1000, 8 bytes
```

R2ILOp
------

`R2ILOp` is the core operation enum with 60+ variants. Each variant has named
fields with `Varnode` inputs and outputs.

### Categories

#### Data Movement

| Operation | Semantics |
|-----------|-----------|
| `Copy` | `dst = src` -- register-to-register copy |
| `Load` | `dst = *[space]addr` -- read from memory |
| `Store` | `*[space]addr = val` -- write to memory |

#### Integer Arithmetic

| Operation | Semantics |
|-----------|-----------|
| `IntAdd` | `dst = a + b` |
| `IntSub` | `dst = a - b` |
| `IntMult` | `dst = a * b` |
| `IntDiv` | `dst = a / b` (unsigned) |
| `IntSDiv` | `dst = a / b` (signed) |
| `IntRem` | `dst = a % b` (unsigned) |
| `IntSRem` | `dst = a % b` (signed) |
| `IntNegate` | `dst = -src` (two's complement) |

#### Logical / Bitwise

| Operation | Semantics |
|-----------|-----------|
| `IntAnd` | `dst = a & b` |
| `IntOr` | `dst = a \| b` |
| `IntXor` | `dst = a ^ b` |
| `IntNot` | `dst = ~src` (bitwise NOT) |
| `BoolAnd` | `dst = a && b` (1-bit) |
| `BoolOr` | `dst = a \|\| b` (1-bit) |
| `BoolXor` | `dst = a ^ b` (1-bit) |
| `BoolNegate` | `dst = !src` (1-bit) |

#### Shift Operations

| Operation | Semantics |
|-----------|-----------|
| `IntLeft` | `dst = a << b` |
| `IntRight` | `dst = a >> b` (logical / unsigned) |
| `IntSRight` | `dst = a >>> b` (arithmetic / signed) |

#### Comparisons

| Operation | Semantics |
|-----------|-----------|
| `IntEqual` | `dst = (a == b)` |
| `IntNotEqual` | `dst = (a != b)` |
| `IntLess` | `dst = (a < b)` unsigned |
| `IntSLess` | `dst = (a < b)` signed |
| `IntLessEqual` | `dst = (a <= b)` unsigned |
| `IntSLessEqual` | `dst = (a <= b)` signed |
| `IntCarry` | `dst = carry(a + b)` |
| `IntSCarry` | `dst = signed_carry(a + b)` |
| `IntSBorrow` | `dst = signed_borrow(a - b)` |

#### Bit Manipulation

| Operation | Semantics |
|-----------|-----------|
| `Piece` | `dst = (hi << n) \| lo` -- concatenate two values |
| `Subpiece` | `dst = src[offset..offset+dst.size]` -- extract bytes |
| `IntZExt` | `dst = zero_extend(src)` |
| `IntSExt` | `dst = sign_extend(src)` |
| `PopCount` | `dst = popcount(src)` |
| `LzCount` | `dst = leading_zeros(src)` |

#### Control Flow

| Operation | Semantics |
|-----------|-----------|
| `Branch` | Unconditional jump to target |
| `CBranch` | If cond then jump to target |
| `BranchInd` | Indirect jump (target is register) |
| `Call` | Call subroutine |
| `CallInd` | Indirect call |
| `Return` | Return from subroutine |

#### Floating Point

| Operation | Semantics |
|-----------|-----------|
| `FloatAdd` | `dst = a + b` (float) |
| `FloatSub` | `dst = a - b` (float) |
| `FloatMult` | `dst = a * b` (float) |
| `FloatDiv` | `dst = a / b` (float) |
| `FloatNeg` | `dst = -src` (float) |
| `FloatAbs` | `dst = abs(src)` (float) |
| `FloatSqrt` | `dst = sqrt(src)` |
| `FloatEqual` | `dst = (a == b)` (float) |
| `FloatLess` | `dst = (a < b)` (float) |
| `FloatNaN` | `dst = isnan(src)` |
| `Int2Float` | `dst = (float)src` |
| `Float2Int` | `dst = (int)src` |
| `Float2Float` | `dst = (float_wider)src` |
| `FloatCeil` | `dst = ceil(src)` |
| `FloatFloor` | `dst = floor(src)` |
| `FloatRound` | `dst = round(src)` |
| `Trunc` | `dst = trunc(src)` |

#### Special

| Operation | Semantics |
|-----------|-----------|
| `CallOther` | Architecture-specific operation (userop index + inputs) |
| `Nop` | No operation |

R2ILBlock
---------

An `R2ILBlock` groups the operations for a single machine instruction:

```rust
pub struct R2ILBlock {
    pub addr: u64,                      // Instruction address
    pub size: u32,                      // Instruction size in bytes
    pub ops: Vec<R2ILOp>,              // Semantic operations
    pub switch_info: Option<SwitchInfo>, // Jump table metadata (if any)
    pub op_metadata: BTreeMap<usize, OpMetadata>, // Sparse op hints by op index
}
```

A single machine instruction typically produces multiple R2ILOps. For example,
x86's `ADD RAX, RBX` generates:

```
IntAdd   { dst: tmp_result,  a: RAX,        b: RBX }
Copy     { dst: RAX,         src: tmp_result }
IntCarry { dst: CF,          a: RAX_old,    b: RBX }
IntEqual { dst: ZF,          a: tmp_result, b: 0 }
IntSLess { dst: SF,          a: tmp_result, b: 0 }
// ... more flag updates
```

The flag computations are generated by the Sleigh specification and are
explicit in r2il. The decompiler later eliminates unused flags
(see [decompiler.md](decompiler.md)).

Validation
----------

r2il now includes a structural validation layer intended to catch malformed
IL before it reaches SSA, decompilation, or plugin analysis paths.

Public API:

```rust
use r2il::{
    validate_archspec, validate_block, validate_block_full, validate_block_semantic, validate_op,
    validate_op_semantic, ValidationError
};
```

Structural checks include:

1. Varnodes:
   - `size > 0`
   - output/destination varnodes are not in `SpaceId::Const`
2. Operations:
   - `Load`/`Store` cannot target `SpaceId::Const`
   - `PtrAdd`/`PtrSub` require `element_size > 0`
   - `Multiequal` inputs are non-empty
   - `CallOther.output` (if present) is not const-space
3. Blocks:
   - `block.size > 0`
   - switch metadata sanity (`min <= max`, case values in range, no duplicate case values)
4. ArchSpec:
   - non-empty `name`
   - `addr_size > 0`, `alignment > 0`
   - at least one address space and exactly one default space
   - unique space IDs and names
   - registers have non-zero size and unique names
   - an empty `register_projections` table means source geometry is unavailable
   - a non-empty projection table is strictly sorted and covers every unique declared register storage exactly once
   - bound projections in one laminar overlap component share its unique declared maximal carrier and one byte orientation
   - partial-overlap components refuse as a whole, and other unprovable geometry carries a typed refusal
   - write effects are not register geometry; they remain instruction-owned P-code/SSA facts

Validation is aggregated: all discovered issues are returned in one
`ValidationError` instead of failing at the first problem.

Semantic checks include:

1. Copy/conversion:
   - `Copy`: `dst.size == src.size`
   - `IntZExt`/`IntSExt`: destination must be larger than source
   - `Trunc`: destination must be smaller than source
2. Integer/bitwise:
   - arithmetic/bitwise binary ops require `a.size == b.size == dst.size`
   - `IntNegate`/`IntNot`: `src.size == dst.size`
   - shifts require `a.size == dst.size` and `shift_amount.size > 0`
   - `IntCarry`/`IntSCarry`/`IntSBorrow`: `a.size == b.size` and `dst.size == 1`
3. Compare/boolean:
   - integer compares require `a.size == b.size` and `dst.size == 1`
   - boolean ops require 1-byte boolean inputs/outputs
4. Memory:
   - `Load`/`Store` address width must match the selected address-space width
   - if a space is unknown/custom, validation falls back to `arch.addr_size`
5. `Piece`/`Subpiece`:
   - `Piece`: `dst.size == hi.size + lo.size`
   - `Subpiece`: `offset < src.size` and `offset + dst.size <= src.size`
6. Control flow:
   - non-const branch/call targets must have `target.size == arch.addr_size`
   - const-space targets are exempt
   - `CBranch.cond.size == 1`

Current scope exclusions (still structural-only): float-family ops, `CallOther`,
`Multiequal`, `Indirect`, `PtrAdd`, `PtrSub`, `SegmentOp`, `New`, `Cast`,
`Extract`, `Insert`, `PopCount`, `Lzcount`.

Validation also includes memory-semantics and topology checks:

1. Arch/topology schema:
   - each `AddressSpace.valid_ranges[i]` must satisfy `start < end`
   - `bank_id` / `segment_id` must be non-empty when present
2. Metadata schema:
   - varnode/op metadata `bank_id` / `segment_id` must be non-empty when present
   - metadata ranges must satisfy `start < end`
3. New op structural checks:
   - `LoadLinked`/`StoreConditional`/`AtomicCAS`/`LoadGuarded`/`StoreGuarded` cannot use const space
4. New op semantic checks:
   - `LoadLinked`: load-style address width checks
   - `StoreConditional`: store-style address width checks
   - `AtomicCAS`: `dst.size == expected.size == replacement.size` + address width
   - `LoadGuarded`/`StoreGuarded`: `guard.size == 1` + address width
5. Const-address enforcement:
   - for const-address memory ops, range/permission checks apply when configured on the target `AddressSpace`
   - symbolic/non-const addresses skip range/permission enforcement

CLI and plugin enforcement:

1. CLI disassembly paths run full validation (`validate_block_full`).
2. Plugin FFI `r2il_block_validate(ctx, block)` now performs full validation
   using `ctx.arch` and reports errors through `r2il_error(ctx)`.

Metadata Hints
--------------

r2il includes a lean metadata layer for advisory hints:

1. `VarnodeMetadata` (attached to `Varnode.meta`):
   - `storage_class`: stack/heap/global/thread_local/const_data/volatile/register/unknown
   - `scalar_kind`: bool/signed_int/unsigned_int/float/bitvector/unknown
   - `pointer_hint`: pointer_like/code_pointer/unknown
   - `float_encoding`: ieee754_binary16/32/64/80/128/unknown
2. `OpMetadata` (attached to `R2ILBlock.op_metadata[index]`):
   - `memory_class`: ram/stack/heap/global/thread_local/mmio/io_port/code/unknown
   - `memory_ordering`: relaxed/acquire/release/acq_rel/seq_cst/unknown
   - `permissions`, `valid_range`, `bank_id`, `segment_id`
   - `atomic_kind`: load_linked/store_conditional/compare_exchange/read_modify_write/fence/unknown

Rules and behavior:

1. Metadata is advisory only and does not alter execution semantics.
2. `Varnode` equality/hash identity remains `(space, offset, size)`; metadata is excluded.
3. Structural validation checks that every `op_metadata` key is in range (`index < ops.len()`).
4. JSON output omits absent metadata fields and emits them only when present.

Example JSON (no metadata):

```json
{"space":"register","offset":0,"size":8}
```

Example JSON (with metadata):

```json
{
  "space":"register",
  "offset":0,
  "size":8,
  "meta":{"scalar_kind":"unsigned_int","pointer_hint":"pointer_like"}
}
```

Unified Instruction Export
--------------------------

r2sleigh includes an instruction-first shared exporter (`r2sleigh-export`) used by CLI
and plugin instruction renderers.

CLI one-liner:

```bash
r2sleigh run --arch x86-64 --bytes "31c00000000000000000000000000000" --action lift --format json
```

Strict action/format matrix:

1. `lift`: `json`, `text`, `esil`, `r2cmd`
2. `ssa`: `json`, `text`
3. `defuse`: `json`, `text`
4. `dec`: `c_like`, `json`, `text`

Unsupported combinations return explicit `UnsupportedCombination` errors.

`r2cmd` output contract:

1. One sidecar comment plus one replay line per op.
2. Sidecar prefix is `# ` and payload is compact single-line JSON.
3. Replay line uses `ae <esil_expression>`.
4. When op metadata exists, sidecar includes `"meta"`; otherwise it is omitted.

Example:

```text
# {"op_index":0,"op":"Copy","op_json":{"Copy":{"dst":{"space":"register","offset":0,"size":8},"src":{"space":"const","offset":0,"size":8}}}}
ae 0,eax,=
```

Endianness Model
----------------

r2il uses explicit endianness fields in `ArchSpec`:

1. `instruction_endianness`
2. `memory_endianness`

`Endianness` enum:

1. `little`
2. `big`
3. `mixed` (reserved)
4. `custom` (reserved)

Optional overrides:

1. `AddressSpace.endianness: Option<Endianness>`
2. `VarnodeMetadata.endianness: Option<Endianness>`
3. `OpMetadata.endianness: Option<Endianness>`

Behavior notes:

1. `mixed` and `custom` are metadata-level only for now; deep execution semantics are deferred.
2. The sole `.r2il` representation is identified by `R2PSTC07`:
   - the wire layout is `R2PSTC07 || payload_length_u64_le || postcard(ArchSpec)`
   - the loader requires an exact payload length and no trailing bytes
   - no independent version field or compatibility decoder exists
   - older versions and alternate encodings are rejected

Memory Semantics + Topology
---------------------------

r2il includes explicit memory semantics ops:

1. `Fence { ordering }`
2. `LoadLinked { dst, space, addr, ordering }`
3. `StoreConditional { result, space, addr, val, ordering }`
4. `AtomicCAS { dst, space, addr, expected, replacement, ordering }`
5. `LoadGuarded { dst, space, addr, guard, ordering }`
6. `StoreGuarded { space, addr, val, guard, ordering }`

`MemoryOrdering` values:

1. `relaxed`
2. `acquire`
3. `release`
4. `acq_rel`
5. `seq_cst`
6. `unknown`

Address-space topology fields (canonical, optional):

1. `memory_class`
2. `permissions` (`read`, `write`, `execute`)
3. `valid_ranges` (half-open `[start, end)`)
4. `bank_id`
5. `segment_id`

Semantic source rule:

1. These operations are emitted only when the loaded Sleigh translator emits
   the corresponding P-code semantics.
2. Mnemonics and userop presentation names never rewrite canonical operations
   or add memory-ordering metadata.
3. A native instruction with no emitted P-code remains an exact native span and
   residualizes as unsupported; it is never replaced with fabricated semantics.

End-to-End Example
------------------

Tracing `mov rax, [rbp-8]` (bytes `48 8b 45 f8`) at address 0x1000:

**P-code** (from libsla):

```
LOAD ram, (RBP + 0xfffffffffffffff8) -> RAX
```

**R2IL**:

```
IntAdd { dst: Unique:0x1000[8], a: Register:0x20[8](RBP), b: Const:0xfffffffffffffff8[8] }
Load   { dst: Register:0x00[8](RAX), space: Ram, addr: Unique:0x1000[8] }
```

**SSA** (after conversion):

```
tmp:1000_1 = rbp_0 + const:fffffffffffffff8_0
rax_1 = *[ram] tmp:1000_1
```

**ESIL**:

```
rbp,0xfffffffffffffff8,+,[8],rax,=
```

**Decompiled C**:

```c
rax = *(rbp - 8);   // or: rax = local_8;
```

Serialization
-------------

r2il types derive `serde::Serialize` and `serde::Deserialize`. The standard
serialization formats are:

- **JSON** (`serde_json`) -- for plugin output and debugging
- **postcard** -- for the sole compact `R2PSTC07` binary storage representation

The plugin command `a:sla.json` outputs the R2ILBlock for the current
instruction as JSON.

Compatibility Guarantees
------------------------

1. The reader accepts exactly the `R2PSTC07` postcard representation.
2. The writer always emits that representation; older artifacts must be regenerated from their source authority.
3. Instruction exporter action/format compatibility is strict:
   - `lift`: `json`, `text`, `esil`, `r2cmd`
   - `ssa`: `json`, `text`
   - `defuse`: `json`, `text`
   - `dec`: `c_like`, `json`, `text`
4. Unsupported action/format pairs return explicit errors.

Versioning policy:

1. The sole binary identity is `R2PSTC07` with a checked payload length.
2. Any other discriminator or encoding is rejected.
