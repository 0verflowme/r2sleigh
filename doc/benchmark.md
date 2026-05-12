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
- invalid JSON from typed/debug report commands
- nondeterministic repeated output
- budget/residual markers in decompile output

The score is intentionally simple. It is not a scientific truth metric; it is a
deterministic triage signal.

Quality Metrics
---------------

The JSON report includes more than pass/fail data:

- decompile classification: `structured`, `residual`, `fallback`, or `empty`
- optional `pdg` comparison when `decompile_pdg` is included in `--commands`
- temp/register artifact density per decompile command
- source smells such as scalar address leaks, synthetic `local_<hex>` stack
  placeholders, and shadowed parameters
- readability smells such as cast noise, pointer-cast noise, stack-address
  leaks, unresolved call names, synthetic type leaks, and unstructured
  `goto`/`while (true)` control flow
- invalid-C readability warnings such as orphan `break;` statements and pointer
  parameters compared directly with non-zero scalar literals
- generic arg/type counts from `a:sla.debug.types`
- runtime buckets: `fast`, `normal`, `slow`, and `hot`
- native radare2 candidate counts with minimal repro commands

These fields are the priority queue for owner-level fixes. A green run with
many residual or temp-heavy outputs is still useful, but it is not the end
state.

Use `--commands decompile_sla,decompile_pdg,types,profile` when the goal is to
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
  --commands decompile_sla,decompile_pdg,types,profile \
  --max-functions 12 \
  --jobs 3 \
  --out /tmp/r2sleigh-all-corpora-pdg.json
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
| command not registered, dylib mismatch | `r2plugin` harness/glue |
| nondeterministic report order | owner producing the unordered data |

Manifest Format
---------------

Use `scripts/setup_corpus.py` to generate the default local manifest, or write a
curated one manually for exact targets:

```json
{
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

Improvement Loop
----------------

1. Run the benchmark for the tier being improved.
2. Sort by low score and slowest commands.
3. Pick one failure family, not one symptom.
4. Fix at the canonical owner.
5. Add a focused unit or `r2r` regression.
6. Rerun the benchmark and compare JSON reports.

The target is not a single perfect score on one binary. The target is a steady
increase in non-fallback decompile rate, summary coverage, type coherence,
symex solve rate, deterministic output, and bounded runtime across the corpus.
