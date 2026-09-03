#!/usr/bin/env bash
# Build this tree's plugin unlocked, then run a command while holding the
# shared install lock.
#
# Every worktree installs to ~/.local/share/radare2/plugins, so anything that
# installs and then measures is measuring whichever tree installed last unless
# the two happen together. That has cost this project five conclusions, and
# every one of them looked like a real finding until it was repeated. Nothing
# about a stale plugin's output says it is stale.
#
# The build is deliberately outside the lock. A cold release build takes
# minutes, and holding the lock through it means nobody measures and nobody
# else can start for the whole time. Building first cuts the held window to the
# install and the measurement, which is the only part that has to be exclusive.
#
# This is the one place that logic lives. tests/corpus/locked_matrix.sh,
# tests/corpus/locked_probe.sh and tests/coverage/locked_coverage.sh each pass
# their own command to it and add nothing else.
#
# usage: tests/locked_run.sh <command> [args ...]
set -euo pipefail

if [[ $# -lt 1 ]]; then
    echo "usage: $0 <command> [args ...]" >&2
    exit 64
fi

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lock=${R2SLEIGH_PLUGIN_LOCK:-/tmp/r2sleigh-plugin-install.lock}
: "${CARGO_TARGET_DIR:=$root/target}"
export CARGO_TARGET_DIR

# What the tree is, right now: the commit, every tracked modification, and the
# names of untracked files. Recomputed after the lock is taken, because the
# build below happens outside it and the command inside it builds again. A tree
# edited during the wait would therefore be measured instead of the tree the
# caller built, and the caller would have no way to tell.
# Every git call is allowed to fail. A tree that is not a checkout still has a
# run to do, and a fingerprint that cannot be taken must skip the comparison
# rather than kill the run: an abort with no message is the failure mode this
# guard exists to prevent, and it would be absurd to add one while adding it.
tree_fingerprint() {
    {
        git -C "$root" rev-parse HEAD 2>/dev/null || true
        git -C "$root" diff HEAD --binary 2>/dev/null || true
        git -C "$root" ls-files --others --exclude-standard 2>/dev/null || true
    } | shasum -a 256 | cut -d' ' -f1
}
before=$(tree_fingerprint)

# One cleanup for everything this script owns, armed before anything is
# started. Releasing the lock was already here; reaping the build is new, and it
# is not a nicety. Killing this script does not kill the cargo it started, and
# an orphaned cargo goes on holding the artifact directory and fights whichever
# build comes next -- twice today an agent cancelled a queued run and then spent
# time on a build that was losing to its own predecessor. Job control puts the
# build in its own process group so the negative pid reaps rustc with it.
build_pid=""
cleanup() {
    if [[ -n $build_pid ]]; then
        kill -- -"$build_pid" 2>/dev/null || kill "$build_pid" 2>/dev/null || true
        wait "$build_pid" 2>/dev/null || true
    fi
    rmdir "$lock" 2>/dev/null || true
}
trap cleanup EXIT INT TERM

echo "building $root without the lock" >&2
set -m
cargo build --release --features all-archs -p r2sleigh-plugin \
    --manifest-path "$root/Cargo.toml" >&2 &
build_pid=$!
wait "$build_pid"
set +m
build_pid=""

echo "waiting for $lock" >&2
# The holder records its process id, and a waiter reclaims the lock when that
# process is gone. Without this a holder killed with a signal its trap cannot
# catch leaves the directory behind and every later run waits on it forever,
# which is a guard that can never clear -- the same defect class as one that can
# never fire. Reclaiming is safe because the directory is the lock: whoever
# recreates it is the new holder, and a live holder is never displaced.
until mkdir "$lock" 2>/dev/null; do
    holder=$(cat "$lock/owner" 2>/dev/null || echo "")
    if [[ -n $holder ]] && ! kill -0 "$holder" 2>/dev/null; then
        echo "lock holder $holder is gone; reclaiming" >&2
        rm -rf "$lock"
        continue
    fi
    sleep 10
done
printf '%s\n' "$$" > "$lock/owner" 2>/dev/null || true
echo "lock taken" >&2

# Tell the command which directory the lock is, so it may hand it back as soon
# as it is finished with the installed plugin rather than at exit. Only the
# capture half of a corpus run needs exclusivity; compiles, oracle runs and
# verification do not, and with six worktrees queued that is hours. A command
# that ignores this behaves exactly as before, because cleanup below tolerates
# finding the directory already gone.
export R2SLEIGH_PLUGIN_LOCK_HELD="$lock"

after=$(tree_fingerprint)
if [[ -n $before && $before != $after ]]; then
    cat >&2 <<'CHANGED'
the tree changed while this run waited for the lock

The build happened before the lock and the command inside it builds again, so
continuing would install and measure the edited tree while reporting it as the
one that was built. That is the stale-plugin hazard turned inside out, and it is
silent: nothing about the output would say which tree it describes.

Nothing was installed. Re-run when the tree is settled, and do not edit while a
locked run is queued.
CHANGED
    exit 75
fi

"$@"
