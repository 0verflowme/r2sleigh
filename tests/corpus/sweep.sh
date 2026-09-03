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

# Helpers the corpus functions call. They are not scored -- verify_rendering.py
# names the scored functions -- but a rendered call needs the callee's
# definition in the same translation unit, so the verifier looks for a section
# by this name and uses it when the caller declares that callee, transitively.
# At -O1 and above a helper may be inlined and the symbol gone, which the
# verifier treats as "no callee section" rather than as a failure.
case $corpus in
    hashes)
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
        callees=(
            rotl32
        )
        ;;
    shapes)
        functions=(
            shape_variadic
            shape_variadic_local
            shape_call_chain
            shape_struct_pointer
            shape_struct_value
            shape_struct_array
            shape_stack_buffer
            shape_recurse_direct
            shape_recurse_mutual
            shape_signed_divmod
            shape_multiword_return
            shape_pointer_to_pointer
            shape_function_pointer
        )
        callees=(
            vfold
            shape_step
            shape_stash
            mixed_touch
            mixed_fold
            shape_mutual_even
            shape_mutual_odd
            wide_make
            indirect_load
            indirect_store
            op_add
            op_xor
            op_mul
        )
        ;;
    *)
        echo "unknown corpus: $corpus" >&2
        exit 64
        ;;
esac

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
