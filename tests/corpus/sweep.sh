#!/bin/bash
# Render the explicit 9-function binding corpus with machine-readable markers.
set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "usage: $0 <corpus-binary>" >&2
    exit 64
fi

binary=$1
if [[ ! -r "$binary" ]]; then
    echo "corpus binary is not readable: $binary" >&2
    exit 66
fi

r2_bin=$(command -v r2) || {
    echo "radare2 executable not found" >&2
    exit 69
}

functions=(
    fnv1a32
    fnv1a64
    djb2
    sdbm
    adler32
    crc32_bitwise
    murmur3_32
    xxhash32
    pearson
)

command_text="a:sla; aaa"
for function in "${functions[@]}"; do
    command_text+="; ?e R2SLEIGH_CORPUS_BEGIN__${function}"
    command_text+="; s sym._${function}"
    command_text+="; pdd"
    command_text+="; ?e R2SLEIGH_CORPUS_END__${function}"
done

echo "R2SLEIGH_CORPUS_TOOL__$r2_bin"
"$r2_bin" -v | head -n 1
echo "R2SLEIGH_CORPUS_BINARY__$binary"
"$r2_bin" -e scr.color=0 -q -c "$command_text" "$binary" 2>&1
