#!/usr/bin/env bash
# Run the whole-binary coverage sweep against a plugin this tree actually built.
#
# The lock, and why the build sits outside it, are explained once in
# tests/locked_run.sh. run_coverage.sh installs before it sweeps, so the
# install and every sweep after it are one critical section.
#
# usage: tests/coverage/locked_coverage.sh [--accept-baseline]
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
exec "$root/tests/locked_run.sh" "$root/tests/coverage/run_coverage.sh" "$@"
