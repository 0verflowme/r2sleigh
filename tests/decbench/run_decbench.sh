#!/usr/bin/env bash
# Measure this tree over every DecBench sailr project and optimization level.
#
# Defaults are the acceptance population: all 26 sailr projects at O0/O1/O2.
# One DecBench invocation owns every selected optimization of a project, so its
# compiled binaries are shared by r2sleigh and (when needed) the cached angr
# reference. Completed projects are checkpointed independently for resume.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
host=${R2SLEIGH_DECBENCH_HOST:-contabo}
baseline="$root/tests/decbench/baseline.json"
run_root=${R2SLEIGH_DECBENCH_REMOTE_ROOT:-/root/r2sleigh-decbench-runs}
fork_remote=${R2SLEIGH_R2_FORK_REMOTE:-/root/r2sleigh-fork-radare2}
workers=${R2SLEIGH_DECBENCH_WORKERS:-4}
expected_project_count=${R2SLEIGH_DECBENCH_SAILR_COUNT:-26}
accept=0
refresh_reference=0
gc_force=0
keep_remote=0
plan_only=0
resume_id=
shard_index=0
shard_count=1
requested_project_count=0
requested_opt_count=0
declare -a requested_projects=()
declare -a requested_opts=()

usage() {
    cat <<'EOF'
usage: tests/decbench/run_decbench.sh [options]

Sweep selection (defaults to all 26 sailr projects at O0, O1 and O2):
  --project NAME       select a project; repeatable
  --opt-level OPT      select O0, O1 or O2; repeatable
  --shard INDEX/COUNT  select a deterministic zero-based project shard

Execution:
  --resume RUN_ID      resume an interrupted remote run
  --workers N          DecBench worker count (default: 4)
  --refresh-reference  run angr even when this version is cached
  --accept-baseline    merge this selection into baseline.json
  --keep-remote        retain the completed remote directory
  --plan               print the checked selection without starting a run
  --host SSH_ALIAS     benchmark host (default: contabo)

Cleanup:
  --gc                 list collectable remote run directories
  --gc-force           collect finished/stale remote run directories
EOF
}

while [[ $# -gt 0 ]]; do
    case $1 in
        --accept-baseline) accept=1; shift ;;
        --refresh-reference) refresh_reference=1; shift ;;
        --keep-remote) keep_remote=1; shift ;;
        --plan) plan_only=1; shift ;;
        --project)
            requested_projects+=("$2")
            requested_project_count=$((requested_project_count + 1))
            shift 2
            ;;
        --opt-level)
            requested_opts+=("$2")
            requested_opt_count=$((requested_opt_count + 1))
            shift 2
            ;;
        --shard)
            if [[ $2 != */* ]]; then
                echo "--shard must be INDEX/COUNT" >&2
                exit 64
            fi
            shard_index=${2%/*}
            shard_count=${2#*/}
            shift 2
            ;;
        --resume) resume_id=$2; shift 2 ;;
        --workers) workers=$2; shift 2 ;;
        --host) host=$2; shift 2 ;;
        --gc-force) gc_force=1; shift; set -- --gc "$@" ;;
        --gc)
            if [[ $run_root != /* || $run_root == / || $run_root == /root ]]; then
                echo "unsafe remote run root: $run_root" >&2
                exit 64
            fi
            ssh -o ServerAliveInterval=30 -o ServerAliveCountMax=6 -o TCPKeepAlive=yes \
                "$host" "GC_FORCE='$gc_force' GC_ROOT='$run_root' bash -s" <<'GC'
set -euo pipefail
now=$(date -u +%s)
force=${GC_FORCE:-0}
for dir in "${GC_ROOT:?}"/*/; do
    [ -d "$dir" ] || continue
    marker="$dir/.running"
    age=$(( now - $(stat -c %Y "$dir" 2>/dev/null || echo "$now") ))
    if [ -f "$marker" ]; then
        started=$(cat "$marker" 2>/dev/null || echo "$now")
        if [ $(( now - started )) -lt 86400 ]; then
            echo "live, left alone: $dir"
            continue
        fi
        why="marker older than a day"
    elif [ -f "$dir/.complete" ]; then
        why="finished run"
    elif [ "$age" -lt 86400 ]; then
        echo "interrupted but resumable, left alone: $dir"
        continue
    else
        why="interrupted and older than a day"
    fi
    if [ "$force" != 1 ]; then
        echo "would collect ($why): $dir"
        continue
    fi
    rm -rf -- "$dir"
    echo "collected ($why): $dir"
done
GC
            exit 0
            ;;
        --help|-h) usage; exit 0 ;;
        *) usage >&2; exit 64 ;;
    esac
done

if [[ $run_root != /* || $run_root == / || $run_root == /root ]]; then
    echo "unsafe remote run root: $run_root" >&2
    exit 64
fi
if [[ ! $workers =~ ^[1-9][0-9]*$ ]]; then
    echo "workers must be a positive integer" >&2
    exit 64
fi
if [[ ! $shard_index =~ ^[0-9]+$ || ! $shard_count =~ ^[1-9][0-9]*$ ]] \
    || (( shard_index >= shard_count )); then
    echo "invalid zero-based shard $shard_index/$shard_count" >&2
    exit 64
fi
if (( requested_opt_count == 0 )); then
    requested_opts=(O0 O1 O2)
else
    for opt in "${requested_opts[@]}"; do
        case $opt in O0|O1|O2) ;; *) echo "unsupported optimization: $opt" >&2; exit 64 ;; esac
    done
fi

ssh_keepalive=(-o ServerAliveInterval=30 -o ServerAliveCountMax=6 -o TCPKeepAlive=yes)
remote_project_listing=$(ssh "${ssh_keepalive[@]}" "$host" \
    "find /root/decbench/projects/sailr -maxdepth 1 -type f -name '*.toml' -printf '%f\\n' | sed 's/\\.toml$//' | sort")
declare -a all_projects=()
while IFS= read -r name; do
    [[ -n $name ]] && all_projects+=("$name")
done <<<"$remote_project_listing"
if (( ${#all_projects[@]} != expected_project_count )); then
    echo "expected $expected_project_count sailr projects, host has ${#all_projects[@]}" >&2
    printf '  %s\n' "${all_projects[@]}" >&2
    exit 70
fi

declare -a candidates=()
if (( requested_project_count == 0 )); then
    candidates=("${all_projects[@]}")
else
    for wanted in "${requested_projects[@]}"; do
        found=0
        for available in "${all_projects[@]}"; do
            if [[ $wanted == "$available" ]]; then
                found=1
                break
            fi
        done
        if (( ! found )); then
            echo "unknown sailr project: $wanted" >&2
            exit 64
        fi
        candidates+=("$wanted")
    done
fi

declare -a projects=()
for ((i = 0; i < ${#candidates[@]}; i++)); do
    if (( i % shard_count == shard_index )); then
        projects+=("${candidates[$i]}")
    fi
done
if (( ${#projects[@]} == 0 )); then
    echo "shard $shard_index/$shard_count selects no projects" >&2
    exit 64
fi

required_metrics=(byte_match ged vj_ged type_match)
available_metrics=$(ssh "${ssh_keepalive[@]}" "$host" \
    "cd /root/decbench && ./venv/bin/python -c 'import decbench.metrics; from decbench.metrics.registry import MetricRegistry; print(\" \".join(sorted(MetricRegistry.list_registered())))'")
vj_ged_source=native
for metric in "${required_metrics[@]}"; do
    if [[ " $available_metrics " != *" $metric "* ]]; then
        if [[ $metric == vj_ged ]] && ssh "${ssh_keepalive[@]}" "$host" \
            "test -f /root/decbench/decbench/metrics/vj_ged.py"; then
            vj_ged_source="tree compatibility registration of DecBench's vj_ged helper"
        else
            echo "required DecBench metric is unavailable on $host: $metric" >&2
            echo "registered metrics: $available_metrics" >&2
            exit 70
        fi
    fi
done

decbench_commit=$(ssh "${ssh_keepalive[@]}" "$host" \
    "git -C /root/decbench rev-parse HEAD")
angr_version=$(ssh "${ssh_keepalive[@]}" "$host" \
    "cd /root/decbench && ./venv/bin/python -c 'import importlib.metadata; print(importlib.metadata.version(\"angr\"))'")
baseline_version=$(python3 - "$baseline" <<'PY'
import json, sys
from pathlib import Path
p = Path(sys.argv[1])
d = json.loads(p.read_text()) if p.exists() else {}
print((d.get("reference") or {}).get("version") or "")
PY
)
baseline_cells=$(python3 - "$baseline" "${required_metrics[@]}" <<'PY'
import json, sys
from pathlib import Path
p = Path(sys.argv[1])
d = json.loads(p.read_text()) if p.exists() else {}
required = set(sys.argv[2:])
selection = set((d.get("selection") or {}).get("cells") or [])
reference = d.get("reference") or {}
metric_cells = reference.get("metric_cells")
if metric_cells is None:
    metrics = set(reference.get("metrics") or [])
    if not metrics:
        metrics = set(((d.get("summary") or {}).get("metrics") or {}))
    complete = selection if required <= metrics else set()
else:
    complete = set(selection)
    for metric in required:
        complete &= set(metric_cells.get(metric) or [])
print("\n".join(sorted(complete)))
PY
)

refresh_all_reference=$refresh_reference
reference_reason="explicit refresh"
if [[ $angr_version != "$baseline_version" ]]; then
    refresh_all_reference=1
    reference_reason="angr version changed (${baseline_version:-uncached} -> $angr_version)"
fi
declare -a project_reference_flags=()
declare -a reference_projects=()
reference_project_count=0
for project in "${projects[@]}"; do
    include_project_reference=$refresh_all_reference
    if (( ! include_project_reference )); then
        for opt in "${requested_opts[@]}"; do
            if ! grep -Fqx "$project/$opt" <<<"$baseline_cells"; then
                include_project_reference=1
                break
            fi
        done
    fi
    project_reference_flags+=("$include_project_reference")
    if (( include_project_reference )); then
        reference_projects+=("$project")
        reference_project_count=$((reference_project_count + 1))
    fi
done
if (( reference_project_count == 0 )); then
    reference_reason="angr $angr_version is cached for every selected cell"
elif (( ! refresh_all_reference )); then
    reference_reason="baseline lacks selected cells for: ${reference_projects[*]}"
fi

echo "population ${#projects[@]}/${#all_projects[@]} sailr projects, ${#requested_opts[@]} opt levels"
echo "shard      $shard_index/$shard_count"
printf 'projects   %s\n' "${projects[*]}"
printf 'opts       %s\n' "${requested_opts[*]}"
echo "metrics    ${required_metrics[*]}"
echo "vj_ged     $vj_ged_source"
echo "decbench   $decbench_commit"
echo "reference  $reference_reason"
echo "execution  one build/decompile/evaluate invocation per project for all selected opts"
if (( plan_only )); then
    exit 0
fi

run_started=$(date -u +%s)
disk_available_before=$(ssh "${ssh_keepalive[@]}" "$host" \
    "df -B1 --output=avail '$run_root' | tail -1 | tr -d ' '")
tree_commit=$(git -C "$root" rev-parse HEAD)
tree_fingerprint=$(
    { git -C "$root" rev-parse HEAD; git -C "$root" diff --no-ext-diff --binary HEAD; } \
        | shasum -a 256 | awk '{print $1}'
)
if [[ -n $resume_id ]]; then
    if [[ ! $resume_id =~ ^decbench-[A-Za-z0-9._-]+$ ]]; then
        echo "invalid resume run id: $resume_id" >&2
        exit 64
    fi
    run_id=$resume_id
else
    run_id="decbench-$(date -u +%Y%m%dT%H%M%S)-$$"
fi
remote="$run_root/$run_id"
private_home="$remote/home"
artifact_root="$root/tests/decbench/artifacts/$run_id"

selection_projects=$(IFS=,; echo "${projects[*]}")
selection_opts=$(IFS=,; echo "${requested_opts[*]}")
selection_reference_projects=
if (( reference_project_count > 0 )); then
    selection_reference_projects=$(IFS=,; echo "${reference_projects[*]}")
fi
if [[ -n $resume_id ]]; then
    resume_metadata=$(ssh "${ssh_keepalive[@]}" "$host" "cat '$remote/run.meta' 2>/dev/null" || true)
    if [[ -z $resume_metadata ]]; then
        echo "no resumable run metadata at $remote" >&2
        exit 66
    fi
    for expected in \
        "tree_fingerprint=$tree_fingerprint" \
        "projects=$selection_projects" \
        "opts=$selection_opts" \
        "decbench_commit=$decbench_commit" \
        "angr_version=$angr_version" \
        "reference_projects=$selection_reference_projects"; do
        if ! grep -Fqx "$expected" <<<"$resume_metadata"; then
            echo "resume metadata mismatch: $expected" >&2
            exit 70
        fi
    done
    witness=$(ssh "${ssh_keepalive[@]}" "$host" "cat '$remote/witness'")
    echo "resuming   $run_id"
else
    witness="r2sleigh-witness-${tree_commit:0:12}-$(date -u +%s)"
    ssh "${ssh_keepalive[@]}" "$host" "test ! -e '$remote' && mkdir -p '$remote/results' '$remote/completed' '$remote/logs' '$remote/witness-checks' '$remote/tree'"
    ssh "${ssh_keepalive[@]}" "$host" "cat > '$remote/run.meta'" <<EOF
tree_commit=$tree_commit
tree_fingerprint=$tree_fingerprint
projects=$selection_projects
opts=$selection_opts
decbench_commit=$decbench_commit
angr_version=$angr_version
reference_projects=$selection_reference_projects
vj_ged_source=$vj_ged_source
EOF
    ssh "${ssh_keepalive[@]}" "$host" "printf '%s\n' '$witness' > '$remote/witness'"
    git -C "$root" ls-files -z \
        | rsync -a -e "ssh ${ssh_keepalive[*]}" --files-from=- --from0 \
            "$root/" "$host:$remote/tree/"
    ssh "${ssh_keepalive[@]}" "$host" "cat >> '$remote/tree/crates/r2engine/src/lib.rs'" <<EOF
#[used]
#[unsafe(no_mangle)]
pub static DECBENCH_WITNESS: &str = "$witness";
EOF
fi

echo "run        $run_id"
echo "witness    $witness"
ssh "${ssh_keepalive[@]}" "$host" "date -u +%s > '$remote/.running'"
cleanup_marker() {
    ssh "${ssh_keepalive[@]}" "$host" "rm -f -- '$remote/.running'" 2>/dev/null || true
}
trap cleanup_marker EXIT

# The plugin C is compiled against this repository's radare2 fork. Synchronize
# tracked fork files before installing; the stamp describes copied content, not
# the host checkout's unrelated .git HEAD.
fork_local=${R2SLEIGH_R2_FORK:-$(cd "$root/.." && pwd)/radare2}
if [[ -d $fork_local/.git ]]; then
    want=$(git -C "$fork_local" rev-parse HEAD)
    have=$(ssh "${ssh_keepalive[@]}" "$host" \
        "cat '$fork_remote/.r2sleigh-synced-from' 2>/dev/null" || true)
    if [[ $want != "$have" ]]; then
        echo "radare2 fork: syncing and rebuilding $want"
        git -C "$fork_local" ls-files -z \
            | rsync -a -e "ssh ${ssh_keepalive[*]}" --files-from=- --from0 \
                "$fork_local/" "$host:$fork_remote/"
        ssh "${ssh_keepalive[@]}" "$host" "FORK_REMOTE='$fork_remote' WANT='$want' bash -s" <<'REMOTE'
set -euo pipefail
cd "$FORK_REMOTE"
git config --global --add safe.directory "$FORK_REMOTE" 2>/dev/null || true
find . -name '*.o' -newer configure -delete 2>/dev/null || true
./configure --prefix=/usr/local >/tmp/r2-configure.log 2>&1 || { tail -20 /tmp/r2-configure.log; exit 70; }
make -j4 >/tmp/r2-make.log 2>&1 || { tail -30 /tmp/r2-make.log; exit 70; }
make install >/tmp/r2-install.log 2>&1 || { tail -20 /tmp/r2-install.log; exit 70; }
printf '%s\n' "$WANT" > "$FORK_REMOTE/.r2sleigh-synced-from"
radare2 -v | head -1
REMOTE
    else
        echo "radare2 fork: host already at $want"
    fi
fi

# HOME remains private so another worktree cannot replace this run's plugin.
# Cargo and rustup state are explicitly shared: leaving them under private HOME
# duplicated 2.2 GB per run even though the benchmark output was only 1.6 MB.
if ! ssh "${ssh_keepalive[@]}" "$host" \
    "HOME='$private_home' WITNESS='$witness' bash -s" <<'VERIFY'
set -euo pipefail
lib=$(find "$HOME/.local/share/radare2/plugins" -name 'libr2sleigh_plugin.*' -print -quit 2>/dev/null || true)
[ -n "$lib" ] && grep -a -q "$WITNESS" "$lib"
VERIFY
then
    ssh "${ssh_keepalive[@]}" "$host" \
        "REMOTE='$remote' PRIVATE_HOME='$private_home' FORK_REMOTE='$fork_remote' WITNESS='$witness' bash -s" <<'INSTALL'
set -euo pipefail
mkdir -p "$PRIVATE_HOME"
export HOME="$PRIVATE_HOME"
export CARGO_HOME=/root/.cargo
export RUSTUP_HOME=/root/.rustup
export CARGO_TARGET_DIR=${R2SLEIGH_DECBENCH_TARGET:-/root/decbench-shared-target}
cd "$REMOTE/tree"
LOCAL_R2_DIR="$FORK_REMOTE" make -C r2plugin RUST_FEATURES=all-archs install >"$REMOTE/install.log" 2>&1 || {
    tail -30 "$REMOTE/install.log"
    exit 70
}
lib=$(find "$PRIVATE_HOME/.local/share/radare2/plugins" -name 'libr2sleigh_plugin.*' -print -quit)
[ -n "$lib" ] || { echo "no plugin library was installed" >&2; exit 70; }
grep -a -q "$WITNESS" "$lib" || {
    echo "the installed library is not this tree: witness absent" >&2
    exit 70
}
echo "installed $lib, witness present"
INSTALL
else
    echo "resumed plugin install, witness present"
fi

for ((project_index = 0; project_index < ${#projects[@]}; project_index++)); do
    project=${projects[$project_index]}
    include_reference=${project_reference_flags[$project_index]}
    if ssh "${ssh_keepalive[@]}" "$host" "test -f '$remote/completed/$project'"; then
        echo "resume: $project already complete"
        continue
    fi
    echo "project $project (${requested_opts[*]})"
    ssh "${ssh_keepalive[@]}" "$host" \
        "REMOTE='$remote' PRIVATE_HOME='$private_home' PROJECT='$project' OPTS='$selection_opts' WORKERS='$workers' INCLUDE_REFERENCE='$include_reference' WITNESS='$witness' bash -s" <<'RUN'
set -euo pipefail
work="$REMOTE/work/$PROJECT"
mkdir -p "$work" "$REMOTE/results" "$REMOTE/logs" "$REMOTE/witness-checks"
lib=$(find "$PRIVATE_HOME/.local/share/radare2/plugins" -name 'libr2sleigh_plugin.*' -print -quit)
[ -n "$lib" ] || { echo "no private plugin before $PROJECT" >&2; exit 70; }
grep -a -q "$WITNESS" "$lib" || {
    echo "witness absent before $PROJECT" >&2
    exit 70
}
: >"$REMOTE/witness-checks/$PROJECT.tsv"
IFS=, read -r -a opts <<<"$OPTS"
for opt in "${opts[@]}"; do
    printf '%s\t%s\t%s\n' "$PROJECT" "$opt" "$WITNESS" \
        | tee -a "$REMOTE/witness-checks/$PROJECT.tsv"
    echo "witness verified: $PROJECT/$opt"
done

stop="$work/.monitor-stop"
samples="$REMOTE/logs/$PROJECT.disk.tsv"
rm -f -- "$stop"
monitor() {
    while [ ! -f "$stop" ]; do
        used=$(du -sb "$REMOTE" 2>/dev/null | awk '{print $1}')
        avail=$(df -B1 --output=avail "$REMOTE" | tail -1 | tr -d ' ')
        printf '%s\t%s\t%s\n' "$(date -u +%s)" "${used:-0}" "${avail:-0}" >>"$samples"
        sleep 15
    done
}
monitor &
monitor_pid=$!
started=$(date -u +%s)

export HOME="$PRIVATE_HOME"
export CARGO_HOME=/root/.cargo
export RUSTUP_HOME=/root/.rustup
cd /root/decbench
cmd=(./venv/bin/python "$REMOTE/tree/tests/decbench/decbench_cli.py" run "projects/sailr/$PROJECT.toml")
for opt in "${opts[@]}"; do cmd+=(-O "$opt"); done
cmd+=(-d r2sleigh)
if [ "$INCLUDE_REFERENCE" = 1 ]; then cmd+=(-d angr); fi
cmd+=(-m ged -m vj_ged -m byte_match -m type_match -j "$WORKERS" -o "$work/out")
set +e
"${cmd[@]}" 2>&1 | tee "$REMOTE/logs/$PROJECT.log" | sed "s/^/  $PROJECT: /"
status=${PIPESTATUS[0]}
set -e
touch "$stop"
wait "$monitor_pid"
if [ "$status" -ne 0 ]; then exit "$status"; fi
test -f "$work/out/function_results.json"
cp "$work/out/function_results.json" "$REMOTE/results/$PROJECT.json"
cp "$work/out/scoreboard.toml" "$REMOTE/results/$PROJECT.scoreboard.toml"
ended=$(date -u +%s)
bytes=$(du -sb "$work" | awk '{print $1}')
printf '%s\t%s\t%s\n' "$PROJECT" "$((ended - started))" "$bytes" \
    >>"$REMOTE/project-stats.tsv"
printf '%s\n' "$ended" >"$REMOTE/completed/$PROJECT"
rm -rf -- "$work"
RUN
done

mkdir -p "$artifact_root/raw"
for project in "${projects[@]}"; do
    scp "${ssh_keepalive[@]}" -q "$host:$remote/results/$project.json" \
        "$artifact_root/raw/$project.json"
    scp "${ssh_keepalive[@]}" -q "$host:$remote/results/$project.scoreboard.toml" \
        "$artifact_root/raw/$project.scoreboard.toml"
done
scp "${ssh_keepalive[@]}" -q "$host:$remote/run.meta" "$artifact_root/run.meta"
scp "${ssh_keepalive[@]}" -q "$host:$remote/project-stats.tsv" "$artifact_root/project-stats.tsv"
mkdir -p "$artifact_root/witness-checks"
for project in "${projects[@]}"; do
    scp "${ssh_keepalive[@]}" -q "$host:$remote/witness-checks/$project.tsv" \
        "$artifact_root/witness-checks/$project.tsv"
    scp "${ssh_keepalive[@]}" -q "$host:$remote/logs/$project.disk.tsv" \
        "$artifact_root/$project.disk.tsv"
done

expected_witness_checks=$(( ${#projects[@]} * ${#requested_opts[@]} ))
actual_witness_checks=$(awk 'NF { n++ } END { print n + 0 }' "$artifact_root"/witness-checks/*.tsv)
if (( actual_witness_checks != expected_witness_checks )); then
    echo "witness coverage mismatch: $actual_witness_checks/$expected_witness_checks" >&2
    exit 70
fi
echo "witness checks: $actual_witness_checks/$expected_witness_checks project/opt runs"

merge_args=(--output "$artifact_root/function_results.json")
for project in "${projects[@]}"; do
    merge_args+=(--input "$artifact_root/raw/$project.json")
    for opt in "${requested_opts[@]}"; do
        merge_args+=(--expected-cell "$project/$opt")
    done
done
python3 "$root/tests/decbench/merge_decbench.py" "${merge_args[@]}"
cp "$artifact_root/function_results.json" "$root/tests/decbench/artifacts/function_results.json"

report_args=(
    --results "$artifact_root/function_results.json"
    --baseline "$baseline"
)
if (( accept )); then report_args+=(--accept-baseline); fi
set +e
python3 "$root/tests/decbench/report_decbench.py" "${report_args[@]}"
report_status=$?
set -e

if (( keep_remote )); then
    ssh "${ssh_keepalive[@]}" "$host" \
        "rm -f -- '$remote/.running'; date -u +%s > '$remote/.complete'"
    echo "remote run retained for --resume/--gc: $remote"
else
    ssh "${ssh_keepalive[@]}" "$host" "rm -rf -- '$remote'"
    echo "garbage-collected finished remote run: $remote"
fi
trap - EXIT

run_finished=$(date -u +%s)
wall_seconds=$((run_finished - run_started))
disk_available_after=$(ssh "${ssh_keepalive[@]}" "$host" "df -B1 --output=avail '$run_root' | tail -1 | tr -d ' '")
peak_run_bytes=$(awk 'BEGIN { m=0 } { if ($2 > m) m=$2 } END { print m }' "$artifact_root"/*.disk.tsv)
min_disk_available=$(awk 'BEGIN { m=0 } { if (m == 0 || $3 < m) m=$3 } END { print m }' \
    "$artifact_root"/*.disk.tsv)
peak_host_disk_bytes=$((disk_available_before - min_disk_available))
retained_host_disk_bytes=$((disk_available_before - disk_available_after))
if (( peak_host_disk_bytes < 0 )); then peak_host_disk_bytes=0; fi
if (( retained_host_disk_bytes < 0 )); then retained_host_disk_bytes=0; fi
selected_cells=$(( ${#projects[@]} * ${#requested_opts[@]} ))
full_cells=$(( expected_project_count * 3 ))
full_wall_seconds=$(( wall_seconds * full_cells / selected_cells ))
printf 'cost: end-to-end wall %ss; peak run directory %.2f GiB; peak host disk %.2f GiB; retained host disk %.2f GiB\n' \
    "$wall_seconds" \
    "$(awk -v n="$peak_run_bytes" 'BEGIN { print n / 1073741824 }')" \
    "$(awk -v n="$peak_host_disk_bytes" 'BEGIN { print n / 1073741824 }')" \
    "$(awk -v n="$retained_host_disk_bytes" 'BEGIN { print n / 1073741824 }')"
printf 'full 26x3 extrapolation: %.2f hours serial; %.2f GiB peak with per-project GC\n' \
    "$(awk -v n="$full_wall_seconds" 'BEGIN { print n / 3600 }')" \
    "$(awk -v n="$peak_run_bytes" 'BEGIN { print n / 1073741824 }')"
exit "$report_status"
