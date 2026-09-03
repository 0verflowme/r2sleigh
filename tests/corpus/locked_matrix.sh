#!/usr/bin/env bash
# Run the corpus matrix against a plugin this tree actually built.
#
# The lock, and why the build sits outside it, are explained once in
# tests/locked_run.sh. run_matrix.sh installs before it captures, so the
# install and the capture are one critical section.
#
# usage: tests/corpus/locked_matrix.sh [--gate <gate>] [extra run_matrix args]
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
exec "$root/tests/locked_run.sh" "$root/tests/corpus/run_matrix.sh" "$@"
