#!/bin/bash
# Build, render, and measure the complete 9-function x 6-configuration matrix.
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
                echo "--gate requires measurement, snapshot, raw, differential, binding-audit, effect-audit, placement-audit, render-audit, noise, native-admission, or cutover" >&2
                exit 64
            fi
            gate=$2
            shift 2
            ;;
        *)
            echo "usage: $0 [--accept-baseline] [--gate measurement|snapshot|raw|differential|binding-audit|effect-audit|placement-audit|render-audit|noise|native-admission|cutover]" >&2
            exit 64
            ;;
    esac
done
if [[ -z $gate ]]; then
    echo "--gate is required: measurement, snapshot, raw, differential, binding-audit, effect-audit, placement-audit, render-audit, noise, native-admission, or cutover" >&2
    exit 64
fi
case $gate in
    measurement|snapshot|raw|differential|binding-audit|effect-audit|placement-audit|render-audit|noise|native-admission|cutover) ;;
    *)
        echo "unsupported gate: $gate" >&2
        exit 64
        ;;
esac

mkdir -p "$artifact_root/bin" "$artifact_root/dumps" "$artifact_root/results"

git_tree_status=$(git -C "$repo_root" status --porcelain --untracked-files=no)
if [[ $gate == cutover && -n $git_tree_status ]]; then
    echo "cutover gate requires a clean tracked worktree" >&2
    exit 65
fi

install_log="$artifact_root/plugin-install.log"
make -C "$repo_root/r2plugin" RUST_FEATURES=all-archs install 2>&1 | tee "$install_log"
if ! grep -q '^Installed to ' "$install_log"; then
    echo "plugin install did not report its destination" >&2
    exit 70
fi

provenance="$artifact_root/provenance.txt"
{
    echo "git_head=$(git -C "$repo_root" rev-parse HEAD)"
    echo "git_branch=$(git -C "$repo_root" branch --show-current)"
    if [[ -n $git_tree_status ]]; then
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
    binary="$artifact_root/bin/h_${config}"
    oracle="$artifact_root/bin/oracle_${config}"
    dump="$artifact_root/dumps/out_${config}.txt"

    clang -arch "$arch" "-O$level" -o "$binary" "$script_dir/hashes.c"
    clang -arch "$arch" "-O$level" -std=c11 -Wall -Wextra -Wpedantic -Werror \
        -o "$oracle" "$script_dir/oracle.c"
    "$script_dir/sweep.sh" "$binary" > "$dump"

    verify_args=(
        "$config"
        --input "$dump"
        --binary "$binary"
        --oracle "$oracle"
        --artifact-root "$artifact_root"
    )
    python3 "$script_dir/verify_rendering.py" "${verify_args[@]}"

    if [[ $gate == cutover ]]; then
        repeat_root="$artifact_root/repeat"
        repeat_dump="$repeat_root/dumps/out_${config}.txt"
        mkdir -p "$repeat_root/dumps"
        "$script_dir/sweep.sh" "$binary" > "$repeat_dump"
        python3 "$script_dir/verify_rendering.py" \
            "$config" \
            --input "$repeat_dump" \
            --binary "$binary" \
            --oracle "$oracle" \
            --artifact-root "$repeat_root"
    fi
done

python3 - "$artifact_root/results" "$script_dir/raw-baseline-sha256.json" \
    "$accept_baseline" "$gate" "$artifact_root/repeat/results" <<'PY'
import json
import os
import sys
import tempfile
from pathlib import Path

result_dir = Path(sys.argv[1])
baseline_path = Path(sys.argv[2])
accept_baseline = sys.argv[3] == "1"
gate = sys.argv[4]
repeat_result_dir = Path(sys.argv[5])
configs = ("x64_O0", "x64_O1", "x64_O2", "arm64_O0", "arm64_O1", "arm64_O2")
functions = (
    "fnv1a32", "fnv1a64", "djb2", "sdbm", "adler32", "crc32_bitwise",
    "murmur3_32", "xxhash32", "pearson",
)
reports = [json.loads((result_dir / f"{config}.json").read_text()) for config in configs]
entries = [entry for report in reports for entry in report["entries"]]
repeat_entries = {}
if gate == "cutover":
    repeat_reports = [
        json.loads((repeat_result_dir / f"{config}.json").read_text())
        for config in configs
    ]
    repeat_entries = {
        (entry["config"], entry["function"]): entry
        for report in repeat_reports
        for entry in report["entries"]
    }
if len(entries) != 54:
    raise SystemExit(f"matrix is incomplete: expected 54 entries, found {len(entries)}")
keys = {(entry["config"], entry["function"]) for entry in entries}
expected_keys = {(config, function) for config in configs for function in functions}
if keys != expected_keys:
    missing = sorted(expected_keys - keys)
    unexpected = sorted(keys - expected_keys)
    raise SystemExit(f"matrix key mismatch: missing={missing} unexpected={unexpected}")
if gate == "cutover" and (
    len(repeat_entries) != 54 or set(repeat_entries) != expected_keys
):
    missing = sorted(expected_keys - set(repeat_entries))
    unexpected = sorted(set(repeat_entries) - expected_keys)
    raise SystemExit(
        "repeat matrix key mismatch: "
        f"count={len(repeat_entries)} missing={missing} unexpected={unexpected}"
    )

if accept_baseline:
    raw_hashes = {}
    for entry in entries:
        generation = entry["generation"]
        if generation.get("section_count") != 1 or "section_sha256" not in generation:
            raise SystemExit(
                f"cannot accept incomplete baseline: {entry['config']}/{entry['function']}"
            )
        key = f"{entry['config']}/{entry['function']}"
        raw_hashes[key] = generation["section_sha256"]
    if set(raw_hashes) != {f"{config}/{function}" for config, function in expected_keys}:
        raise SystemExit("refusing to write a partial raw baseline")
    payload = {"schema_version": 1, "raw_sha256": dict(sorted(raw_hashes.items()))}
    baseline_path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w", dir=baseline_path.parent, prefix=".raw-baseline.", delete=False
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
        (result_dir / f"{report['config']}.json").write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n"
        )

combined = {"schema_version": 1, "expected_entries": 54, "entries": entries}
(result_dir / "matrix.json").write_text(json.dumps(combined, indent=2, sort_keys=True) + "\n")

for score in (
    "generation", "raw", "diagnostic", "differential", "snapshot",
    "binding_audit", "effect_obligations", "placement_audit", "render_refusal",
):
    counts = {}
    for entry in entries:
        status = entry[score]["status"]
        counts[status] = counts.get(status, 0) + 1
    print(f"{score}: {dict(sorted(counts.items()))}")
print(f"matrix={result_dir / 'matrix.json'}")

failures = []
common_case_ids = [
    *(f"boundary:{length}" for length in (0, 1, 2, 3, 4, 7, 8, 15, 16, 17, 31, 32, 61)),
    *(f"random:{length}" for length in (5, 12, 24, 63, 96)),
]
seeded_functions = {"murmur3_32", "xxhash32"}
default_seeds = {"murmur3_32": 0x9747B28C, "xxhash32": 0}
for entry in entries:
    key = f"{entry['config']}/{entry['function']}"
    if (
        entry["generation"].get("section_count") != 1
        or "section_sha256" not in entry["generation"]
    ):
        failures.append(f"{key}: generation section is not uniquely accounted")
    if entry["raw"]["status"] == "not_run":
        failures.append(f"{key}: raw was not measured")
    if entry["diagnostic"]["status"] == "not_run":
        failures.append(f"{key}: diagnostic was not measured")
    if entry["differential"]["status"] == "not_run":
        failures.append(f"{key}: differential was not measured")
    if gate == "binding-audit" and entry["binding_audit"]["status"] != "pass":
        failures.append(
            f"{key}: binding_audit={entry['binding_audit']['status']}"
        )
    if gate == "effect-audit" and entry["effect_obligations"]["status"] != "pass":
        effect = entry["effect_obligations"]
        failures.append(
            f"{key}: effect_obligations={effect['status']} "
            f"source={effect.get('source_status')}"
        )
    if gate == "placement-audit" and entry["placement_audit"]["status"] != "pass":
        placement = entry["placement_audit"]
        failures.append(
            f"{key}: placement_audit={placement['status']} "
            f"source={placement.get('source_status')}"
        )
    if gate in {"noise", "cutover"} and entry["machine_noise"]["status"] != "pass":
        noise = entry["machine_noise"]
        detail = " ".join(
            f"{name}={noise['counts'][name]}" for name in noise.get("failing", ())
        )
        failures.append(f"{key}: machine_noise={noise['status']} {detail}".rstrip())
    if gate == "render-audit" and entry["render_refusal"]["status"] != "pass":
        render = entry["render_refusal"]
        failures.append(
            f"{key}: render_refusal={render['status']} "
            f"source={render.get('source_status')}"
        )
    if gate in {"native-admission", "cutover"}:
        binding = entry["binding_audit"]
        effect = entry["effect_obligations"]
        placement = entry["placement_audit"]
        render = entry["render_refusal"]
        request_statuses = {
            binding.get("request_status"),
            effect.get("request_status"),
            placement.get("request_status"),
            render.get("request_status"),
        }
        if (
            request_statuses != {"completed"}
            or binding["status"] != "pass"
            or effect["status"] != "pass"
            or placement["status"] != "pass"
            or render["status"] != "pass"
        ):
            failures.append(
                f"{key}: native_admission requests={sorted(map(str, request_statuses))} "
                f"binding={binding['status']} effect={effect['status']} "
                f"placement={placement['status']} render={render['status']}"
            )
    if gate in {"snapshot", "raw", "differential"} and entry["snapshot"]["status"] not in {
        "match", "accepted"
    }:
        failures.append(f"{key}: snapshot={entry['snapshot']['status']}")
    if gate in {"raw", "differential", "cutover"} and entry["raw"]["status"] != "pass":
        failures.append(f"{key}: raw={entry['raw']['status']}")
    if gate in {"differential", "cutover"} and (
        entry["differential"]["status"] != "pass"
        or entry["differential"].get("basis") != "raw"
    ):
        failures.append(
            f"{key}: differential={entry['differential']['status']} "
            f"basis={entry['differential'].get('basis')}"
        )
    if gate in {"differential", "cutover"}:
        expected_case_ids = list(common_case_ids)
        if entry["function"] in seeded_functions:
            seed_values = dict.fromkeys(
                (0, 1, default_seeds[entry["function"]], 0xFFFFFFFF, 0x13579BDF)
            )
            expected_case_ids.extend(f"seed:{seed}" for seed in seed_values)
        actual_cases = entry["differential"].get("cases", [])
        actual_case_ids = [case.get("case_id") for case in actual_cases]
        if actual_case_ids != expected_case_ids or any(
            case.get("status") != "pass" for case in actual_cases
        ):
            failures.append(
                f"{key}: differential case set/status does not match the required vector set"
            )
    if gate == "cutover":
        repeated = repeat_entries.get((entry["config"], entry["function"]))
        if repeated is None:
            failures.append(f"{key}: missing deterministic repeat entry")
        elif repeated["generation"].get("section_sha256") != entry["generation"].get(
            "section_sha256"
        ):
            failures.append(f"{key}: raw rendering changed across repeated generation")
if failures:
    print("gate failures:", file=sys.stderr)
    for failure in failures:
        print(f"  {failure}", file=sys.stderr)
    raise SystemExit(1)
PY
