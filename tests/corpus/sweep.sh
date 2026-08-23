#!/bin/bash
# pdd — r2sleigh's renderer. NOT pdc (radare2's own pseudo-decompiler).
BIN="$1"
FUNCS="fnv1a32 fnv1a64 djb2 sdbm adler32 fletcher32 crc32_bitwise crc32_init crc32_table murmur3_32 xxhash32 siphash24 pearson combined"
CMD="a:sla; aaa"
for f in $FUNCS; do CMD="$CMD; ?e ════════════════ $f; s sym._$f; pdd"; done
r2 -e scr.color=0 -q -c "$CMD" "$BIN" 2>&1
