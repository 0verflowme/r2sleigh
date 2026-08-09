#!/bin/sh
set -eu

library=$1
if [ "$(uname -s)" = Darwin ]; then
	symbols=$(nm -gU "$library" | awk '{ print $NF }')
else
	symbols=$(nm -g --defined-only "$library" | awk '{ print $NF }')
fi

for forbidden in \
	r2sleigh_engine_decompile_function \
	r2sleigh_engine_type_function_json \
	r2sleigh_ffi_sizeof_function_context \
	r2sleigh_ffi_alignof_function_context \
	r2sleigh_ffi_sizeof_engine_decompile_input \
	r2sleigh_ffi_alignof_engine_decompile_input
do
	if printf '%s\n' "$symbols" | grep -Eq "^_?${forbidden}$"; then
		echo "forbidden legacy engine symbol remains: ${forbidden}" >&2
		exit 1
	fi
done

if ! printf '%s\n' "$symbols" | grep -Eq '^_?r2sleigh_api_v2$'; then
	echo "native V2 API symbol is missing" >&2
	exit 1
fi
