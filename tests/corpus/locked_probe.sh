#!/usr/bin/env bash
# Run one r2 command against a plugin this tree actually built.
#
# Every worktree installs to ~/.local/share/radare2/plugins, so a bare `r2 -c
# pdd` measures whichever tree installed last. That has now cost this project
# five conclusions -- four before this file existed and one after -- and every
# one of them looked like a real finding until it was repeated. Writing the
# hazard down did not stop it, because the failure is silent: nothing about a
# stale plugin's output says it is stale.
#
# So this builds first without the lock, then holds
# /tmp/r2sleigh-plugin-install.lock across the install and the command
# together, which is the only window in which the answer is about this tree.
#
# usage: tests/corpus/locked_probe.sh <binary> <r2 command> [env=value ...]
#   tests/corpus/locked_probe.sh /bin/ls 'a:sla; aaa; pdd @@F'
#   tests/corpus/locked_probe.sh ./h_x64_O2 'a:sla; aaa; s sym._djb2; pdd' R2SLEIGH_TIMING=1
set -euo pipefail

if [[ $# -lt 2 ]]; then
    echo "usage: $0 <binary> <r2 command> [env=value ...]" >&2
    exit 64
fi

binary=$1
command=$2
shift 2

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)

# The measurement and the install are one critical section. Releasing between
# them is what makes a stale answer possible, so both run inside the lock.
exec "$root/tests/locked_run.sh" bash -c '
    set -euo pipefail
    root=$1
    binary=$2
    command=$3
    shift 3
    make -C "$root/r2plugin" RUST_FEATURES=all-archs install >&2
    env "$@" r2 -e scr.color=0 -q -c "$command" "$binary"
' locked-probe "$root" "$binary" "$command" "$@"
