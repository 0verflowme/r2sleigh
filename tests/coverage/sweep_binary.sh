#!/bin/bash
# Decompile every function radare2 finds in one binary, with markers.
set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "usage: $0 <binary>" >&2
    exit 64
fi

binary=$1
if [[ ! -r "$binary" ]]; then
    echo "binary is not readable: $binary" >&2
    exit 66
fi

r2_bin=$(command -v r2) || {
    echo "radare2 executable not found" >&2
    exit 69
}

# The function list goes to a temporary file rather than beside the binary.
# Writing `$binary.functions` works for a corpus binary this harness compiled
# into its own artifact directory and fails for anything under a system path,
# which is exactly the input the harness most needs to sweep.
functions=$(mktemp -t r2sleigh-coverage-functions)
trap 'rm -f "$functions"' EXIT

# One analysis pass, then one seek-and-decompile per function. `afl` is read
# from the same session that renders, so the function set and the renderings
# cannot come from different analyses.
"$r2_bin" -e scr.color=0 -q -c 'a:sla; aaa; afl' "$binary" 2>/dev/null \
    | awk '$1 ~ /^0x/ { print $1, $2, $NF }' > "$functions"

command_text="a:sla; aaa"
while read -r addr size name; do
    command_text+="; ?e R2SLEIGH_COV_BEGIN__${name}__${size}"
    command_text+="; s ${addr}"
    command_text+="; pdd"
    command_text+="; ?e R2SLEIGH_COV_END__${name}"
done < "$functions"

echo "R2SLEIGH_COV_BINARY__$binary"
"$r2_bin" -e scr.color=0 -q -c "$command_text" "$binary" 2>&1
