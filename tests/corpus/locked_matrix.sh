#!/usr/bin/env bash
# Run the corpus matrix while several worktrees share one installed plugin.
#
# Every worktree installs to ~/.local/share/radare2/plugins, and run_matrix.sh
# captures its dumps against whatever is installed at that moment. Two runs
# overlapping therefore measure each other's build, which this project has
# already voided four conclusions to. So the install and everything after it
# happen under /tmp/r2sleigh-plugin-install.lock.
#
# The build does not. run_matrix.sh's first act is `make install`, which builds
# before it installs, so taking the lock and then calling it holds the lock
# through a cold release build -- minutes during which nobody measures and
# nobody else can start. Building first, unlocked, cuts the held time to the
# install and the capture.
#
# usage: tests/corpus/locked_matrix.sh [--gate <gate>] [extra run_matrix args]
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
lock=${R2SLEIGH_PLUGIN_LOCK:-/tmp/r2sleigh-plugin-install.lock}
: "${CARGO_TARGET_DIR:=$root/target}"
export CARGO_TARGET_DIR

echo "building the plugin without the lock"
cargo build --release --features all-archs -p r2sleigh-plugin --manifest-path "$root/Cargo.toml"

echo "waiting for $lock"
until mkdir "$lock" 2>/dev/null; do
    sleep 10
done
# Released on any exit, so an interrupted run does not strand the queue.
trap 'rmdir "$lock" 2>/dev/null || true' EXIT
echo "lock taken"

"$root/tests/corpus/run_matrix.sh" "$@"
