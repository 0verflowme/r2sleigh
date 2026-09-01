#!/bin/bash
# Whole-binary render coverage: every function radare2 finds, not a named few.
#
# The 54-cell matrix scores nine hand-picked functions and checks that what they
# render is correct. That is a canary and does not answer the other question --
# how much of a binary renders at all -- which was measured by hand, and was
# wrong twice: once by a factor of six, because import thunks were counted as
# functions, and once by fourteen refusals, because the number was carried
# forward from an older tree instead of remeasured.
#
# This decompiles every function in the corpus binaries and records, per
# function, whether it rendered and the typed cause when it did not. The
# baseline is blessed like the raw one. A function that rendered and now
# refuses fails the gate; a function that now renders is reported and needs
# --accept-baseline to be recorded.
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(cd "$script_dir/../.." && pwd)
corpus_dir="$repo_root/tests/corpus"
artifact_root="$script_dir/artifacts"
baseline_path="$script_dir/coverage-baseline.json"
accept_baseline=0

while [[ $# -gt 0 ]]; do
    case $1 in
        --accept-baseline)
            accept_baseline=1
            shift
            ;;
        *)
            echo "usage: $0 [--accept-baseline]" >&2
            exit 64
            ;;
    esac
done

mkdir -p "$artifact_root/bin" "$artifact_root/dumps"

install_log="$artifact_root/plugin-install.log"
make -C "$repo_root/r2plugin" RUST_FEATURES=all-archs install 2>&1 | tee "$install_log"
if ! grep -q '^Installed to ' "$install_log"; then
    echo "plugin install did not report its destination" >&2
    exit 70
fi

configs=(x64_O0 x64_O1 x64_O2 arm64_O0 arm64_O1 arm64_O2)
arches=(x86_64 x86_64 x86_64 arm64 arm64 arm64)
levels=(0 1 2 0 1 2)
sources=(hashes branchy)

for index in "${!configs[@]}"; do
    config=${configs[$index]}
    arch=${arches[$index]}
    level=${levels[$index]}
    for source in "${sources[@]}"; do
        binary="$artifact_root/bin/${source}_${config}"
        clang -arch "$arch" "-O$level" -o "$binary" "$corpus_dir/${source}.c"
        "$script_dir/sweep_binary.sh" "$binary" > "$artifact_root/dumps/${source}_${config}.txt"
    done
done

python3 "$script_dir/report_coverage.py" \
    --artifact-root "$artifact_root" \
    --baseline "$baseline_path" \
    --clang "$(clang --version | head -n 1)" \
    $([[ $accept_baseline == 1 ]] && echo --accept-baseline)
