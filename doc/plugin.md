radare2 Plugin
==============

Architecture
------------

The r2sleigh radare2 plugin consists of two layers:

1. Rust cdylib (libr2sleigh_plugin.so) -- exports C-ABI functions
2. C wrapper (r_anal_sleigh.c) -- implements RAnalPlugin/RArchPlugin

Architecture Detection
----------------------

Reads anal.arch and anal.bits from radare2:
- x86 + 64 bits -> x86-64
- x86 + 32 bits -> x86
- arm -> arm
- riscv + 64 bits -> riscv64
- riscv + 32 bits -> riscv32
- mips -> mips

Override with: a:sla.arch x86-64

Plugin Callbacks
----------------

sleigh_op: Lifts instructions during aaa. Generates ESIL.
sleigh_recover_vars: Provides SSA-derived variables for afva.
sleigh_analyze_fcn: Per-function SSA analysis after af (also auto-applies DATA xrefs).
sleigh_get_data_refs: Def-use xrefs callback used by radare2 during aar when supported.
sleigh_post_analysis: Native post-analysis enrichment during aa/aaa/aaaa.

Command Reference
-----------------

Instruction-Level:
- a:sla -- Status and help
- a:sla.info -- Architecture info
- a:sla.arch [name] -- Get/set architecture
- a:sla.json -- R2IL ops as JSON
- a:sla.regs -- Registers read/written
- a:sla.mem -- Memory accesses
- a:sla.vars -- All varnodes
- a:sla.ssa -- SSA for instruction
- a:sla.defuse -- Def-use analysis

Function-Level:
- a:sla.ssa.func -- Function SSA with phi nodes
- a:sla.ssa.func.opt -- Optimized function SSA
- a:sla.defuse.func -- Function-wide def-use
- a:sla.dom -- Dominator tree
- a:sla.cfg -- ASCII CFG
- a:sla.cfg.json -- CFG as JSON
- a:sla.taint -- Taint analysis
- a:sla.slice [var] -- Backward slice
- pdd -- Decompile through radare2's bounded borrowed-snapshot provider

Both a:sla and a:sleigh prefixes work.

Direct `a:sla.dec` and `a:sla.decj` requests are intentionally unavailable:
they do not run inside radare2's locked snapshot transaction and therefore
cannot construct source authority. `pdd` receives one ABI-138/schema-10 borrowed
snapshot, deep-copies it synchronously, and either completes from that immutable
source or refuses. It never falls back to live blocks, names, or detached test
metadata.

Detached symbolic commands are unavailable for the same reason. This includes
`a:sla.sym`, `a:sla.sym.paths`, `a:sym.runj`, the `a:sym.explore*` and
`a:sym.solve*` families, and commands that construct a symbolic scope from live
plugin state. Symbolic execution requires the same borrowed ABI-138 snapshot;
the plugin does not expose a replacement command or API for detached inputs.

Executable semantic C is authorized only through the generic source-obligation
ledger and typed output-node ownership. Every live machine effect from the
immutable source revision must have exactly one certified typed owner; missing,
duplicate, unsupported, or foreign ownership residualizes or refuses without
falling through to legacy C.

Benchmark-shaped branchless guards and struct-array updates are regression
inputs, not production recognizers or renderer routes. They currently remain
residual until generic typed expression, return, aggregate-memory, and lvalue
regions can close their complete ledgers. Consequently,
`semantic_kernel_render` is present only when a generic certified region owns
the exact source revision; its absence for those fixtures is expected.

Function signatures, layouts, and calling-convention carriers come only from
the immutable radare2 function snapshot. DWARF ingestion is a binary-load
operation in radare2; the plugin never reparses or imports DWARF during
analysis or decompilation.

Snapshot-owned type inference and writeback are not yet exposed through a
radare2 host callback. Direct `a:sla.types` therefore refuses instead of using
detached state. Type/writeback integration tests must not be restored until an
equivalent locked snapshot transaction exists for that host path.

DATA xrefs are applied automatically during function analysis (`af`) and reference
analysis (`aar`) via plugin callbacks.

Instruction Export Path
-----------------------

Instruction-level plugin renderers now use the shared `r2sleigh-export`
pipeline internally:

- `r2il_block_op_json_named`
- `r2il_block_to_esil`
- `r2il_block_to_ssa_json`
- `r2il_block_defuse_json`
- `r2dec_block`

This keeps CLI and plugin output logic aligned. The supported external C ABI is
the versioned V2 function table; retired direct legacy exports are not preserved.

The shared action/format policy is:

- `lift`: `json`, `text`, `esil`, `r2cmd`
- `ssa`: `json`, `text`
- `defuse`: `json`, `text`
- `dec`: `c_like`, `json`, `text`

Endianness
----------

Canonical endianness fields live in `ArchSpec` (`instruction_endianness`,
`memory_endianness`). The retired direct `r2il_is_big_endian` export is not part
of the V2 ABI.

Configuration
-------------

`a:sla.mem` JSON is backward compatible and keeps legacy keys:

- `addr`
- `size`
- `write`

When available, it also emits additive memory semantics/topology fields:

- `ordering`
- `atomic_kind`
- `guarded`
- `permissions`
- `range`
- `bank_id`
- `segment_id`
- `memory_class`

SLEIGH_TAINT_MAX_BLOCKS: Max blocks for auto-taint. Default 200.
SLEIGH_SIG_WRITEBACK_MAX_BLOCKS: Max blocks for automatic signature/CC write-back. Default 200.
SLEIGH_SIG_MIN_CONFIDENCE: Minimum confidence for signature overwrite. Default 70.
SLEIGH_CC_MIN_CONFIDENCE: Minimum confidence for calling convention overwrite. Default 80.

Native analysis depth:

| Command | r2sleigh behavior |
|---|---|
| `aa` | basic bounded post-analysis |
| `aaa` | balanced signatures, xrefs, and type facts |
| `aaaa` | aggressive taint, interproc, and type write-back |

r2sleigh does not expose public `anal.*` tuning keys. Detailed engine inspection
lives under debug commands such as `a:sla.debug.profilej` and
`a:sla.debug.types`.

Kernel smoke harness:

```bash
R2SLEIGH_KERNELCACHE=/path/to/kernelcache \
  scripts/kernel_smoke.py \
  --r2 /Users/priyanshu/code/radare2/binr/radare2/radare2 \
  --analysis aaaa \
  --strict \
  --out /tmp/r2sleigh-kernel-smoke.json
```

The harness is advisory and local-only: no kernel binaries or generated smoke
reports are committed. It probes representative kernel helpers and records
normalized decompile, type, and profile output for regression triage.
By default the report keeps hashes, sizes, and line counts while redacting the
local kernel path and stdout/stderr previews. Use `--include-sensitive` only for
local triage when full paths and text previews are needed.

Strict mode returns non-zero for missing requested targets, zero discovered
functions, malformed profile/type JSON, decompiler fallback comments, and
radare2 command return failures. The harness mirrors the r2r/e2e plugin
isolation knobs where practical: `--plugin-dir` defaults to
`R2SLEIGH_PLUGIN_DIR`, `R2R_PLUGIN_DIR`, or `R2_LIBR_PLUGINS`, and `--tmpdir`
sets a temporary HOME/XDG/TMP root for radare2 subprocesses.

Automatic Signature Write-Back (aaaa)
-------------------------------------

During `aaaa`, the plugin also performs function signature + calling convention
write-back:

- Builds SSA and infers return/parameter types.
- Applies inferred signatures on any supported loaded architecture via direct `RAnal` update first (`r_anal_str_to_fcn`), then falls back to `afs` if needed.
- Applies inferred calling conventions only when the payload contains a non-empty verified calling convention. In practice this is currently strongest on x86/x86-64.
- Confidence-gated overwrite: signature `>= 70`, calling convention `>= 80`.
- Practical consistency verification is currently disabled by default.
- After verified signature apply, direct caller xrefs are propagated in a
  targeted pass:
  - xref scope: direct `CALL/CODE/JUMP` refs only.
  - caller reanalysis: type-match + `afva` var recovery.
  - each caller function is updated at most once per `aaaa` run.
- Propagation metrics are logged in summary (`prop_*`) with
  `sample_callees=` trace for up to 5 triggered callees.
- Write-back metrics include apply path counters (`sig_api_apply_ok`,
  `sig_api_verify_fail`, `sig_cmd_fallback_attempted`, `sig_cmd_apply_ok`,
  `sig_cmd_apply_fail`, `cc_api_apply_ok`, `cc_api_verify_fail`,
  `cc_cmd_fallback_attempted`, `cc_cmd_apply_ok`, `cc_cmd_apply_fail`).
- Preserves existing function names (no rename during write-back).
- Skips functions above `SLEIGH_SIG_WRITEBACK_MAX_BLOCKS`.
