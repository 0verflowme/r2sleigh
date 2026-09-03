#!/bin/bash
# Build, render, and measure the 13-function x 6-configuration shape matrix.
#
# This is a second semantic gate, deliberately separate from run_matrix.sh.
# run_matrix.sh gates merges on 54 hash cells that all pass; these 78 cells
# cover shapes that corpus cannot express -- a variadic call, a stack frame
# read across calls, structs, arrays, recursion, signed division, a multi-word
# return, a pointer to a pointer, an indirect call -- and many of them are
# expected to be red today. That is the point: a gate that cannot see a defect
# is worse than a red cell, and the three defects found by the external
# benchmark this week were all invisible to the hash corpus.
#
# Gates:
#   shapes-measurement  every cell produced a record. This is the one that can
#                       be required today: it fails only if the harness itself
#                       stopped measuring, not if a rendering is wrong.
#   shapes-snapshot     every rendering matches the recorded baseline hash.
#   shapes-raw          the emitted C compiles strictly for every cell.
#   shapes-differential every cell agrees with the source-built oracle.
#
# Promotion. When a shape's cells reach `pass` on every correctness column, add
# it to REQUIRED_DIFFERENTIAL below and it is gated from then on; when all
# thirteen are listed there, `shapes-differential` becomes the gate CI runs and
# this file's per-shape list can go. Promote a shape only on evidence from a
# locked run -- tests/corpus/locked_shapes.sh -- never from a bare invocation,
# because every worktree installs the plugin to the same place.
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(cd "$script_dir/../.." && pwd)
artifact_root="$script_dir/artifacts"
accept_baseline=0
gate=
while [[ $# -gt 0 ]]; do
    case $1 in
        --accept-baseline)
            accept_baseline=1
            shift
            ;;
        --gate)
            if [[ $# -lt 2 ]]; then
                echo "--gate requires shapes-measurement, shapes-snapshot, shapes-raw, or shapes-differential" >&2
                exit 64
            fi
            gate=$2
            shift 2
            ;;
        *)
            echo "usage: $0 [--accept-baseline] [--gate shapes-measurement|shapes-snapshot|shapes-raw|shapes-differential]" >&2
            exit 64
            ;;
    esac
done
if [[ -z $gate ]]; then
    echo "--gate is required: shapes-measurement, shapes-snapshot, shapes-raw, or shapes-differential" >&2
    exit 64
fi
case $gate in
    shapes-measurement|shapes-snapshot|shapes-raw|shapes-differential) ;;
    *)
        echo "unsupported gate: $gate" >&2
        exit 64
        ;;
esac

mkdir -p "$artifact_root/bin" "$artifact_root/dumps" "$artifact_root/results"

install_log="$artifact_root/plugin-install.log"
make -C "$repo_root/r2plugin" RUST_FEATURES=all-archs install 2>&1 | tee "$install_log"
if ! grep -q '^Installed to ' "$install_log"; then
    echo "plugin install did not report its destination" >&2
    exit 70
fi

provenance="$artifact_root/shapes-provenance.txt"
{
    echo "git_head=$(git -C "$repo_root" rev-parse HEAD)"
    echo "git_branch=$(git -C "$repo_root" branch --show-current)"
    if [[ -n $(git -C "$repo_root" status --porcelain --untracked-files=no) ]]; then
        echo "git_tree=dirty"
    else
        echo "git_tree=clean"
    fi
    echo "clang=$(command -v clang)"
    clang --version | head -n 1
    echo "r2=$(command -v r2)"
    r2 -v | head -n 1
} > "$provenance"

configs=(x64_O0 x64_O1 x64_O2 arm64_O0 arm64_O1 arm64_O2)
arches=(x86_64 x86_64 x86_64 arm64 arm64 arm64)
levels=(0 1 2 0 1 2)

for index in "${!configs[@]}"; do
    config=${configs[$index]}
    arch=${arches[$index]}
    level=${levels[$index]}
    binary="$artifact_root/bin/shapes_${config}"
    oracle="$artifact_root/bin/shapes_oracle_${config}"
    dump="$artifact_root/dumps/shapes_out_${config}.txt"

    clang -arch "$arch" "-O$level" -o "$binary" "$script_dir/shapes.c"
    clang -arch "$arch" "-O$level" -std=c11 -Wall -Wextra -Wpedantic -Werror \
        -o "$oracle" "$script_dir/shapes_oracle.c"
    "$script_dir/sweep.sh" "$binary" shapes > "$dump"

    python3 "$script_dir/verify_rendering.py" \
        "$config" \
        --corpus shapes \
        --input "$dump" \
        --binary "$binary" \
        --oracle "$oracle" \
        --artifact-root "$artifact_root"
done

python3 - "$artifact_root/results" "$script_dir/raw-baseline-shapes-sha256.json" \
    "$accept_baseline" "$gate" <<'PY'
import json
import os
import sys
import tempfile
from pathlib import Path

result_dir = Path(sys.argv[1])
baseline_path = Path(sys.argv[2])
accept_baseline = sys.argv[3] == "1"
gate = sys.argv[4]
sys.path.insert(0, str(baseline_path.parent))
configs = ("x64_O0", "x64_O1", "x64_O2", "arm64_O0", "arm64_O1", "arm64_O2")
import verify_rendering as verifier

functions = tuple(verifier.CORPUS_SPECS["shapes"])
# Shapes whose cells are known green and are gated from now on. Empty until the
# first shape passes on all six configurations; see the promotion note at the
# top of this script.
REQUIRED_DIFFERENTIAL: set[str] = set()

expected_cells = len(configs) * len(functions)
reports = [
    json.loads((result_dir / f"shapes_{config}.json").read_text())
    for config in configs
]
entries = [entry for report in reports for entry in report["entries"]]
if len(entries) != expected_cells:
    raise SystemExit(
        f"shape matrix is incomplete: expected {expected_cells} entries, "
        f"found {len(entries)}"
    )
keys = {(entry["config"], entry["function"]) for entry in entries}
expected_keys = {(config, function) for config in configs for function in functions}
if keys != expected_keys:
    missing = sorted(expected_keys - keys)
    unexpected = sorted(keys - expected_keys)
    raise SystemExit(f"shape matrix key mismatch: missing={missing} unexpected={unexpected}")

if accept_baseline:
    raw_hashes = {}
    for entry in entries:
        generation = entry["generation"]
        if generation.get("section_count") != 1 or "section_sha256" not in generation:
            raise SystemExit(
                f"cannot accept incomplete baseline: {entry['config']}/{entry['function']}"
            )
        raw_hashes[f"{entry['config']}/{entry['function']}"] = generation["section_sha256"]
    payload = {"schema_version": 1, "raw_sha256": dict(sorted(raw_hashes.items()))}
    baseline_path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w", dir=baseline_path.parent, prefix=".raw-baseline-shapes.", delete=False
    ) as temporary:
        json.dump(payload, temporary, indent=2, sort_keys=True)
        temporary.write("\n")
        temporary_path = Path(temporary.name)
    os.replace(temporary_path, baseline_path)
    for report in reports:
        for entry in report["entries"]:
            actual = entry["generation"]["section_sha256"]
            entry["snapshot"] = {
                "status": "accepted",
                "expected_sha256": actual,
                "actual_sha256": actual,
            }
        (result_dir / f"shapes_{report['config']}.json").write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n"
        )

combined = {
    "schema_version": 1,
    "corpus": "shapes",
    "expected_entries": expected_cells,
    "entries": entries,
}
matrix_path = result_dir / "shapes-matrix.json"
matrix_path.write_text(json.dumps(combined, indent=2, sort_keys=True) + "\n")

for score in (
    "generation", "raw", "diagnostic", "differential", "snapshot",
    "binding_audit", "effect_obligations", "placement_audit", "render_refusal",
):
    counts = {}
    for entry in entries:
        counts[entry[score]["status"]] = counts.get(entry[score]["status"], 0) + 1
    print(f"{score}: {dict(sorted(counts.items()))}")

# The per-cell map. This is the deliverable the gate exists for: what this
# decompiler gets wrong outside hash functions, cell by cell.
print()
print("shape cells (raw / differential / named cause):")
for entry in sorted(entries, key=lambda item: (item["function"], item["config"])):
    key = f"{entry['config']}/{entry['function']}"
    differential = entry["differential"]
    generation = entry["generation"]
    detail = ""
    if generation["status"] != "present":
        # The renderer names why it declined, in a comment where the function
        # would have been. That name is the finding; "unparsable" is not.
        detail = generation.get("fallback_reason") or (
            f"{generation['status']}: "
            + str(generation.get("error", "")).strip().splitlines()[0][:160]
        )
    elif entry["raw"]["status"] == "signature_mismatch":
        detail = (
            f"rendered arity {generation.get('rendered_arity')} for a function "
            f"of {generation.get('expected_arity')}"
        )
    elif entry["raw"]["status"] != "pass":
        detail = "raw=" + entry["raw"]["status"]
        for line in str(entry["raw"].get("stderr", "")).splitlines():
            if "error:" in line:
                detail += " :: " + line.split("error:", 1)[1].strip()[:140]
                break
    if differential["status"] not in {"pass", "blocked_generation", "blocked_signature"}:
        for case in differential.get("cases", []):
            if case.get("status") != "pass":
                detail += (
                    f" | {case['case_id']} expected={case.get('expected')} "
                    f"actual={case.get('actual')} ({case['status']})"
                )
                break
    print(
        f"  {key:<40} raw={entry['raw']['status']:<20} "
        f"diff={differential['status']:<20} {detail}"
    )
print()
print(f"matrix={matrix_path}")

failures = []
for entry in entries:
    key = f"{entry['config']}/{entry['function']}"
    if (
        entry["generation"].get("section_count") != 1
        or "section_sha256" not in entry["generation"]
    ):
        failures.append(f"{key}: generation section is not uniquely accounted")
    for score in ("raw", "diagnostic", "differential"):
        if entry[score]["status"] == "not_run":
            failures.append(f"{key}: {score} was not measured")
    gated = gate == "shapes-differential" or entry["function"] in REQUIRED_DIFFERENTIAL
    # Snapshot is its own opt-in gate and is deliberately not implied by the
    # correctness ones. Sixty-four of these cells are refusal comments today;
    # pinning their text as the expected rendering would make every improvement
    # to the decompiler read as a regression, which is the corpus-as-specification
    # mistake this project has already paid for once.
    if gate == "shapes-snapshot" and entry["snapshot"]["status"] not in {
        "match",
        "accepted",
    }:
        failures.append(f"{key}: snapshot={entry['snapshot']['status']}")
    if gate == "shapes-raw" or gated:
        if entry["raw"]["status"] != "pass":
            failures.append(f"{key}: raw={entry['raw']['status']}")
    if gated and (
        entry["differential"]["status"] != "pass"
        or entry["differential"].get("basis") != "raw"
    ):
        failures.append(
            f"{key}: differential={entry['differential']['status']} "
            f"basis={entry['differential'].get('basis')}"
        )
if failures:
    print("gate failures:", file=sys.stderr)
    for failure in failures:
        print(f"  {failure}", file=sys.stderr)
    raise SystemExit(1)
PY
