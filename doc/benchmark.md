Reversing Benchmark
===================

The benchmark loop is the product-quality driver for r2sleigh. It is not a
replacement for `r2r` or unit tests; it is the measurement layer that tells us
which reversing workflows are still weak.

Principles
----------

- Keep binaries local. Do not commit coreutils builds, CGC samples, Juliet
  builds, Apple kernelcaches, or generated benchmark reports.
- Use stable JSON shape and ordering. Reports are intended for diffing between
  revisions; timing fields are retained for performance triage.
- Fix failures at the canonical owner: `../radare2`, `r2ssa`, `r2sym`,
  `r2types`, `r2dec`, or plugin glue only when it is truly integration.
- Treat benchmark failures as work items, not snapshot churn.

Benchmark Tiers
---------------

### Tier 0: Repo Fixtures

The default runner uses the local `tests/e2e/*_x86` binaries when present. This
is the fast sanity tier for decompile, type, symex, taint, and plugin runtime
integration.

```bash
python3 scripts/reversing_benchmark.py \
  --r2 /private/tmp/radare2-r2sleigh-clean/binr/radare2/radare2 \
  --plugin-dir r2plugin \
  --out /tmp/r2sleigh-reversing-benchmark.json
```

### Tier 1: Coreutils

Build GNU coreutils locally under `/tmp/r2sleigh-corpora`, then run the
benchmark from the generated manifest.

```bash
python3 scripts/setup_corpus.py setup --tier coreutils

python3 scripts/reversing_benchmark.py \
  --r2 /private/tmp/radare2-r2sleigh-clean/binr/radare2/radare2 \
  --manifest /tmp/r2sleigh-corpora/manifest.json \
  --max-binaries-per-corpus 12 \
  --out /tmp/r2sleigh-coreutils-benchmark.json
```

This tier is best for decompiler readability, libc helper handling, loops,
string/data references, and deterministic output.

### Tier 2: CGC

Use a local DARPA CGC corpus checkout/build for vulnerability-oriented binary
analysis. This tier stresses path feasibility, symex, memory facts, taint,
worker summaries, and residual diagnostics.

```bash
python3 scripts/setup_corpus.py setup --tier cgc --allow-large-downloads

python3 scripts/reversing_benchmark.py \
  --manifest /tmp/r2sleigh-corpora/manifest.json \
  --analysis aaaa \
  --max-binaries-per-corpus 20 \
  --repeat 2 \
  --out /tmp/r2sleigh-cgc-benchmark.json
```

### Tier 3: Juliet

Compile a selected Juliet C/C++ subset locally. Use this tier for known CWE
patterns and source-level ground truth.

```bash
python3 scripts/setup_corpus.py setup --tier juliet --allow-large-downloads

python3 scripts/reversing_benchmark.py \
  --manifest /tmp/r2sleigh-corpora/manifest.json \
  --analysis aaa \
  --max-binaries-per-corpus 20 \
  --out /tmp/r2sleigh-juliet-benchmark.json
```

### Tier 4: Apple Kernelcache

Use a local kernelcache only. The repo never commits Apple binaries.

```bash
R2SLEIGH_KERNELCACHE=/path/to/kernelcache \
python3 scripts/reversing_benchmark.py \
  --analysis aaaa \
  --repeat 2 \
  --out /tmp/r2sleigh-kernel-benchmark.json
```

For strict target-oriented kernel acceptance, use the dedicated smoke harness:

```bash
R2SLEIGH_KERNELCACHE=/path/to/kernelcache \
python3 scripts/kernel_smoke.py --strict
```

Scoring
-------

Each benchmark case starts at 100 and loses points for:

- native radare2 discovery or CFG failures classified as `radare2_candidate`
- discovery failures or zero recovered functions
- missing requested targets
- command failures
- empty decompiler output
- decompiler fallback markers
- invalid JSON from requested debug report commands
- nondeterministic repeated output
- budget/residual markers in decompile output

The score is intentionally simple. It is not a scientific truth metric; it is a
deterministic triage signal. Source-shape manifest mismatches are recorded as
advisory diagnostics and do not change the score or semantic closure result.

Quality Metrics
---------------

The JSON report includes more than pass/fail data:

- decompile classification: `structured`, `residual`, `fallback`, or `empty`
- optional `pdg` comparison when `decompile_pdg` is included in `--commands`
- optional source-shape advisory status under `summary.quality.gold_oracle`
- owner buckets for actionable fix routing across `../radare2`, `r2ssa`,
  `r2sym`, `r2types`, `r2engine`, `r2dec`, and plugin glue
- `summary.next_work`, a deterministic owner-ranked backlog with target
  examples, setup/command bottleneck status, and PDG quality-gap status
- temp/register artifact density per decompile command
- source smells such as scalar address leaks, synthetic `local_<hex>` stack
  placeholders, and shadowed parameters
- readability smells such as cast noise, pointer-cast noise, stack-address
  leaks, unresolved call names, synthetic type leaks, and unstructured
  `goto`/`while (true)` control flow
- invalid-C readability warnings such as orphan `break;` statements and pointer
  parameters compared directly with non-zero scalar literals
- runtime buckets: `fast`, `normal`, `slow`, and `hot`
- native radare2 candidate counts with minimal repro commands

These fields are the priority queue for owner-level fixes. A green run with
many residual or temp-heavy outputs is still useful, but it is not the end
state.

Start broad-tranche triage from `summary.next_work`. If `status` is
`owner_work`, fix the first `owner_work_items` entry at that canonical owner.
If `status` is `pdg_quality_gap`, compare the listed `pdg` counts and
`summary.quality.pdg_comparison.worst_quality_gaps`. If `status` is
`setup_bottleneck`, improve benchmark batching or setup reuse
before spending time on semantic quality.

Use `--commands decompile_sla,decompile_pdg,ssa_function_report` when the goal is to
beat r2ghidra's `pdg` directly. If r2ghidra is installed outside the temporary
benchmark home, add it explicitly with `--baseline-plugin-dir`, for example
`--baseline-plugin-dir ~/.local/share/radare2/plugins`. The report records
common-target quality wins, latency wins, artifact-count wins, baseline command
failures, and the worst target-level gaps under
`summary.quality.pdg_comparison`. The comparison is also grouped by corpus and
target family so broad runs cannot hide one weak corpus behind another.
Quality/perf wins are counted only for targets where both `decompile_sla` and
`decompile_pdg` completed successfully.

For a broad local acceptance pass over every corpus currently present on the
machine, use the generated manifest plus explicit local corpus directories:

```bash
python3 scripts/reversing_benchmark.py \
  --preset full \
  --r2 /private/tmp/radare2-r2sleigh-clean/binr/radare2/radare2 \
  --plugin-dir r2plugin \
  --baseline-plugin-dir ~/.local/share/radare2/plugins \
  --manifest /tmp/r2sleigh-corpora/manifest.json \
  --coreutils-dir /tmp/r2sleigh-corpora/src/coreutils/coreutils-9.11/src \
  --cgc-dir /tmp/r2sleigh-corpora/cgc \
  --juliet-dir /tmp/r2sleigh-corpora/juliet \
  --commands decompile_sla,decompile_pdg,ssa_function_report \
  --max-functions 12 \
  --jobs 3 \
  --out /tmp/r2sleigh-all-corpora-pdg.json
```

Use strict quality thresholds when the benchmark is acting as an acceptance
gate, not just a report generator:

```bash
python3 scripts/reversing_benchmark.py \
  --preset tier1 \
  --strict \
  --max-hard-failures 0 \
  --max-residual-decompile 0 \
  --min-average-score 99.0 \
  --out /tmp/r2sleigh-coreutils-gate.json
```

Use the closure gate when the benchmark is intended to answer "are we done for
this tranche?" It applies the default closure bar: strict mode, hard failures `0`,
residual decompiles `0`, average score `>= 99.5`, and setup/command ratio
`<= 2.0`. If `decompile_pdg` is included in `--commands`,
it also requires a successful PDG comparison, zero PDG quality wins, and zero
PDG quality-then-performance wins unless explicitly overridden. Raw elapsed
performance is still reported separately so a fast fallback cannot count as a
gold-standard win.

```bash
python3 scripts/reversing_benchmark.py \
  --preset tier1 \
  --closure-gate \
  --coreutils-dir /tmp/r2sleigh-corpora/src/coreutils/coreutils-9.11/src \
  --max-binaries-per-corpus 108 \
  --max-functions 12 \
  --out /tmp/r2sleigh-coreutils-closure.json
```

Use source-shape manifests when PDG/r2ghidra is not enough for readability
comparison. These checks record source-like text that should appear and fake
artifacts that should not appear. They are advisory only: rendered text is not
proof, so these checks cannot authorize C or satisfy semantic closure.

```bash
python3 scripts/reversing_benchmark.py \
  --preset smoke \
  --gold-manifest tests/gold/source_oracle.json \
  --target test_struct_array_index \
  --commands decompile_sla,ssa_function_report \
  --strict \
  --require-gold \
  --out /tmp/r2sleigh-source-gold.json
```

Source-shape manifest expectations match by corpus/case/target/command. `contains` and
`regex` entries must be present in the command output; `not_contains` and
`not_regex` entries must be absent. Set `owner` when the failure should route
directly to a canonical component such as `r2types` or `r2dec`. Use compiled
execution, differential evaluators, and obligation closure for correctness.

Fixed-Runner Performance Gate
-----------------------------

Semantic correctness and performance are separate CI jobs. The performance
gate rejects empty output, fallback output, malformed SSA reports, and missing
in-process timings, but it is not semantic proof: a structurally valid yet
semantically wrong result can still satisfy a latency budget. Use the
compiled/differential r2r and e2e oracles for correctness. The `source-gold`
target remains an advisory source-shape regression report.

`tests/gold/mem_scan2_performance.json` is the versioned Darwin/arm64 O2 fixed
performance contract. It measures the deterministic bounded `fnv_fold` target
and makes no correctness or refusal claim about `mem_scan2`.

The contract runs 20 isolated cold command processes and four fresh warm
sessions with five measured repeats each. Command latency comes from radare2's
in-process `?t` timer and includes only the command body. It excludes r2
startup, setup analysis, sentinel output, and the old pair of `date` subprocess
launches. Nearest-rank p95 is therefore the 19th of 20 latency observations,
not the maximum. Cold RSS still measures each direct child process and warm RSS
measures each fresh batch session; RSS remains a separate gate.

Each p95 has two independent limits:

- a release target with explicit headroom over the reviewed command-body result;
- a regression limit of at most 1.5 times the reviewed in-process reference, plus
  only the small absolute jitter slack declared in the manifest.

The contract measures two atomic commands: certified decompilation and the
exact-target `ssa_function_report`. The latter must return nonempty SSA blocks,
prepared facts, and the selected entry address; it cannot be satisfied by a
passive or previously populated profile accumulator. Reviewed references and
release headroom are recorded directly in the versioned manifest. Release
targets, regression ratios, and RSS limits remain independent.

Availability is executable, not inferred from artifact filenames. Before any
sample is accepted, the harness discovers the exact target and runs plugin help,
architecture status, decompile, and SSA-function-report probes. ABI/load errors,
missing commands, empty/no-op output, fallback decompilation, invalid JSON, or
missing in-process timing cause the required gate to fail closed. Optional local
runs may still report `skipped`; the required CI invocation cannot.

Ordinary machines may run the command and receive an explicit `skipped` report
when the fixed runner or generated test binary is unavailable:

```bash
python3 scripts/reversing_benchmark.py \
  --fixed-performance-gate tests/gold/mem_scan2_performance.json \
  --out /tmp/r2sleigh-fixed-performance.json
```

The required CI job cannot skip. Deployment must provide a self-hosted runner
with the `r2sleigh-perf-v1` label, Darwin/arm64, and the exact runner identity:

```bash
make -C tests/r2r link-bins
make -C r2plugin RUST_FEATURES=all-archs
R2SLEIGH_FIXED_PERF_RUNNER=r2sleigh-darwin-arm64-perf-v1 \
python3 scripts/reversing_benchmark.py \
  --fixed-performance-gate tests/gold/mem_scan2_performance.json \
  --require-fixed-performance \
  --r2 ../radare2/binr/radare2/radare2 \
  --plugin-dir r2plugin \
  --out /tmp/r2sleigh-fixed-performance.json
```

Interpreting Failures
---------------------

Use this ownership map when turning benchmark output into implementation work:

| Failure | First owner to inspect |
| --- | --- |
| `zero_functions`, bad function discovery | `../radare2` typed/native analysis seam |
| missing or unstable SSA/CFG facts | `r2ssa` |
| residual/budgeted symbolic facts | `r2sym` |
| bad return/arg/out-param/type facts | `r2types` |
| fallback, repeated calls, temp-heavy C | `r2dec` |
| advisory source-shape mismatch | manifest `owner` for triage only; never semantic authority or a closure failure |
| timeout or nondeterministic route/budget behavior | `r2engine` |
| command not registered, dylib mismatch | `r2plugin` harness/glue |
| nondeterministic report order | owner producing the unordered data |

Manifest Format
---------------

Use `scripts/setup_corpus.py` to generate the default local manifest, or write a
curated one manually for exact targets:

```json
{
  "availability": [
    {
      "corpus": "coreutils",
      "status": "available",
      "binary_count": 1,
      "skip_reasons": []
    }
  ],
  "binaries": [
    {
      "name": "ls-O2",
      "path": "/path/to/coreutils/bin/ls",
      "corpus": "coreutils",
      "analysis": "aaa",
      "targets": ["main", "decode_switches"],
      "max_functions": 6
    }
  ]
}
```

Run with:

```bash
python3 scripts/reversing_benchmark.py --manifest /path/to/manifest.json
```

`availability` is the setup/discovery gate. A tier with `status: "skipped"` is
not a semantic failure; it means the local corpus is absent or not buildable yet.

Source-gold manifests use a separate top-level `expectations` array:

```json
{
  "schema": 1,
  "expectations": [
    {
      "id": "repo-vuln-struct-array-index",
      "corpus": "repo-fixtures",
      "case": "vuln_test_x86",
      "target": "test_struct_array_index",
      "command": "decompile_sla",
      "owner": "r2types",
      "contains": ["arr[idx].third"],
      "regex": ["DemoStruct\\s*\\*\\s*arr"],
      "not_contains": ["sla_struct_", "*(arr +"]
    }
  ]
}
```

Improvement Loop
----------------

1. Run the benchmark for the tier being improved.
2. Start from `summary.next_work`, then inspect low scores and slowest commands.
3. Pick one failure family, not one symptom.
4. Fix at the canonical owner named by the report.
5. Add a focused unit or `r2r` regression.
6. Rerun the benchmark and compare JSON reports.

The target is not a single perfect score on one binary. The target is a steady
increase in non-fallback decompile rate, summary coverage, type coherence,
symex solve rate, deterministic output, and bounded runtime across the corpus.
