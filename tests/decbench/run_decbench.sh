#!/usr/bin/env bash
# Measure this tree on DecBench, on a Linux host, and compare with the record.
#
# DecBench is the only measurement this project has that scores the *content*
# of a rendered function rather than its shape. `byte_match` recompiles the
# output and compares its assembly to the original; `type_match` scores
# recovered types against DWARF. Until this script existed both were run by
# hand, twice, months apart, and every defect they would have caught went
# unnoticed in between: the argument dropped from a variadic call, the stack
# pointer drifting eight bytes per call site, the register-named local staged
# before every argument. The corpus could not see any of them, because it is
# nine hash functions of one shape.
#
# It runs on a remote Linux host because the benchmark's binaries are ELF built
# by GCC and the metric recompiles them, so the toolchain has to match.
#
# usage: tests/decbench/run_decbench.sh [--accept-baseline] [--host <ssh alias>]
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
host=${R2SLEIGH_DECBENCH_HOST:-contabo}
baseline="$root/tests/decbench/baseline.json"
accept=0
project=${R2SLEIGH_DECBENCH_PROJECT:-projects/sailr/bzip2.toml}
opt=${R2SLEIGH_DECBENCH_OPT:-O0}

while [[ $# -gt 0 ]]; do
    case $1 in
        --accept-baseline) accept=1; shift ;;
        --host) host=$2; shift 2 ;;
        *) echo "usage: $0 [--accept-baseline] [--host <ssh alias>]" >&2; exit 64 ;;
    esac
done

# A private radare2 plugin directory per run. radare2 reads user plugins from
# $HOME, so two trees measuring at once otherwise overwrite each other's
# library and each scores the other's work. This needs no cooperation from
# whoever else is on the host.
run_id="decbench-$(date -u +%Y%m%dT%H%M%S)-$$"
# Runs live under one directory rather than directly in /root, and the
# difference is not cosmetic. Older manual runs left `/root/decbench-*.log`
# files behind, and a cleanup for those also matches `/root/decbench-<stamp>/`,
# which is a live run's tree: two runs here were deleted mid-build by one, and
# the script reported the failure as a missing install log, which reads like a
# build error rather than the tree being pulled out from under it.
run_root=${R2SLEIGH_DECBENCH_REMOTE_ROOT:-/root/r2sleigh-decbench-runs}
remote="$run_root/$run_id"
private_home="$remote/home"
fork_remote=${R2SLEIGH_R2_FORK_REMOTE:-/root/r2sleigh-fork-radare2}

# A string only this tree contains, so a build that failed to install cannot be
# mistaken for a change with no effect. That has already cost two measurements:
# `make install` aborted on stale object files, the previous library stayed in
# place, and the numbers came back identical to the baseline.
witness="r2sleigh-witness-$(git -C "$root" rev-parse --short HEAD)-$(date -u +%s)"

echo "run     $run_id"
echo "witness $witness"

ssh "$host" "mkdir -p '$remote/tree'"
git -C "$root" ls-files -z | rsync -a --files-from=- --from0 "$root/" "$host:$remote/tree/"

# The plugin's C is compiled against the radare2 fork, and this project changes
# that fork. A tree whose C calls an API the host's fork does not have fails to
# build, so the fork travels with the plugin rather than being assumed current.
# The build check below turns that into a loud failure rather than a measurement
# of whatever was installed before, but only if the fork is actually brought up
# to date first.
fork_local=${R2SLEIGH_R2_FORK:-$(cd "$root/.." && pwd)/radare2}
if [ -d "$fork_local/.git" ]; then
    # The comparison is against a stamp this script writes, not against the
    # host's git HEAD: only tracked files are copied, so the host's `.git` never
    # advances and its HEAD would always disagree.
    want=$(git -C "$fork_local" rev-parse HEAD)
    have=$(ssh "$host" "cat '$fork_remote/.r2sleigh-synced-from' 2>/dev/null" || true)
    if [ "$want" != "$have" ]; then
        echo "radare2 fork: host at ${have:-none}, this tree wants $want; syncing and rebuilding"
        git -C "$fork_local" ls-files -z \
            | rsync -a --files-from=- --from0 "$fork_local/" "$host:$fork_remote/"
        ssh "$host" bash -s <<EOF
set -euo pipefail
cd '$fork_remote'
git config --global --add safe.directory '$fork_remote' 2>/dev/null || true
find . -name '*.o' -newer configure -delete 2>/dev/null || true
./configure --prefix=/usr/local >/tmp/r2-configure.log 2>&1 || { tail -20 /tmp/r2-configure.log; exit 70; }
make -j4 >/tmp/r2-make.log 2>&1 || { tail -30 /tmp/r2-make.log; exit 70; }
make install >/tmp/r2-install.log 2>&1 || { tail -20 /tmp/r2-install.log; exit 70; }
printf '%s\n' '$want' > '$fork_remote/.r2sleigh-synced-from'
radare2 -v | head -1
EOF
    else
        echo "radare2 fork: host already at $want"
    fi
fi
# `#[used]` and an exported symbol, not a `const`. A `const` is inlined at
# its use sites and this one has none, so nothing reaches the binary and the
# check below failed on every tree it was ever pointed at -- a guard that
# always fires is as useless as one that never does, and this one hid a
# working install behind a stale-plugin error.
ssh "$host" "cat >> $remote/tree/crates/r2engine/src/lib.rs" <<WITNESS
#[used]
#[unsafe(no_mangle)]
pub static DECBENCH_WITNESS: &str = "$witness";
WITNESS

ssh "$host" bash -s <<EOF
set -euo pipefail
mkdir -p '$private_home'
export HOME='$private_home'
cd '$remote/tree'
LOCAL_R2_DIR='$fork_remote' make -C r2plugin RUST_FEATURES=all-archs install >'$remote/install.log' 2>&1 || {
    # A missing log here does not mean the build failed to write one: the
    # host is shared, and this run's whole tree can be removed underneath it
    # while it builds. Say which happened, because "install failed" sent one
    # reader looking at a compiler for a directory that no longer existed.
    if [ ! -d '$remote/tree' ]; then
        echo "this run's remote tree was removed while it was building" >&2
        exit 72
    fi
    tail -20 '$remote/install.log'; exit 70; }
lib=\$(find '$private_home/.local/share/radare2/plugins' -name 'libr2sleigh_plugin.*' | head -1)
if [ -z "\$lib" ]; then echo "no plugin library was installed" >&2; exit 70; fi
if ! grep -a -q '$witness' "\$lib"; then
    echo "the installed library is not this tree's: witness string absent" >&2
    exit 70
fi
echo "installed \$lib, witness present"
EOF

ssh "$host" bash -s <<EOF
set -euo pipefail
export HOME='$private_home'
cd /root/decbench
# Output streams rather than going to a remote log. A silent run is
# indistinguishable from a hung one, and this measurement has hung twice while
# the host was loaded by other work.
./venv/bin/decbench run '$project' -O '$opt' -d r2sleigh -d angr \
    -m ged -m byte_match -m type_match -j 4 --binary-limit 1 \
    -o '$remote/out' 2>&1 | tee '$remote/decbench.log' | sed 's/^/  decbench: /'
test -f '$remote/out/function_results.json'
EOF

mkdir -p "$root/tests/decbench/artifacts"
scp -q "$host:$remote/out/function_results.json" "$root/tests/decbench/artifacts/function_results.json"
scp -q "$host:$remote/out/scoreboard.toml" "$root/tests/decbench/artifacts/scoreboard.toml"
ssh "$host" "rm -rf '$remote'"

python3 "$root/tests/decbench/report_decbench.py" \
    --results "$root/tests/decbench/artifacts/function_results.json" \
    --baseline "$baseline" \
    $([[ $accept == 1 ]] && echo --accept-baseline)
