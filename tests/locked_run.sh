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

echo "building $root without the lock" >&2
cargo build --release --features all-archs -p r2sleigh-plugin \
    --manifest-path "$root/Cargo.toml" >&2

echo "waiting for $lock" >&2
until mkdir "$lock" 2>/dev/null; do
    sleep 10
done
# Released on any exit, so an interrupted run does not strand the queue.
trap 'rmdir "$lock" 2>/dev/null || true' EXIT
echo "lock taken" >&2

"$@"
