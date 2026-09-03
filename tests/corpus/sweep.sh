#!/bin/bash
# Render one corpus binary's functions with machine-readable markers.
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
    echo "usage: $0 <corpus-binary> [hashes|shapes]" >&2
    exit 64
fi

binary=$1
corpus=${2:-hashes}
if [[ ! -r "$binary" ]]; then
    echo "corpus binary is not readable: $binary" >&2
    exit 66
fi

r2_bin=$(command -v r2) || {
    echo "radare2 executable not found" >&2
    exit 69
}

# The scored functions and the helpers they call both come from
# verify_rendering.py, which is the one place that knows what a corpus is made
# of. The helpers are not scored, but a rendered call needs the callee's
# definition in the same translation unit, so the verifier looks for a section
# by this name and uses it when the caller declares that callee, transitively.
# At -O1 and above a helper may be inlined and the symbol gone, which the
# verifier treats as "no callee section" rather than as a failure.
script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
names=$(python3 "$script_dir/corpus_names.py" "$corpus") || {
    echo "could not read the corpus function list for $corpus" >&2
    exit 70
}
read -r -a functions <<<"$(printf '%s\n' "$names" | sed -n 1p)"
read -r -a callees <<<"$(printf '%s\n' "$names" | sed -n 2p)"
if [[ ${#functions[@]} -eq 0 ]]; then
    echo "corpus $corpus has no scored functions" >&2
    exit 70
fi

command_text="a:sla; aaa"
for function in "${functions[@]}" "${callees[@]}"; do
    command_text+="; ?e R2SLEIGH_CORPUS_BEGIN__${function}"
    command_text+="; s sym._${function}"
    command_text+="; pdd"
    command_text+="; ?e R2SLEIGH_CORPUS_END__${function}"
done

echo "R2SLEIGH_CORPUS_TOOL__$r2_bin"
"$r2_bin" -v | head -n 1
echo "R2SLEIGH_CORPUS_BINARY__$binary"
R2SLEIGH_BINDING_AUDIT=1 \
    "$r2_bin" -e scr.color=0 -q -c "$command_text" "$binary" 2>&1
