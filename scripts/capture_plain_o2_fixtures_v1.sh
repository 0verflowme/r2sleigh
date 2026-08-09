#!/bin/bash

set -euo pipefail

if [ "$#" -ne 1 ]; then
	printf 'usage: %s OUTPUT_DIRECTORY\n' "$0" >&2
	exit 2
fi

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
manifest="$repo_root/tests/r2r/fixtures/plain_o2_v1/manifest.json"
output_dir="$1"
r2_bin="${R2SLEIGH_CAPTURE_R2:-r2}"

mkdir -p "$output_dir/core" "$output_dir/sleigh"

for tool in file jq nm otool shasum; do
	command -v "$tool" >/dev/null || {
		printf 'missing required tool: %s\n' "$tool" >&2
		exit 1
	}
done
command -v "$r2_bin" >/dev/null || {
	printf 'radare2 is unavailable: %s\n' "$r2_bin" >&2
	exit 1
}

verify_hash() {
	local path="$1"
	local expected="$2"
	local actual
	actual="$(shasum -a 256 "$path" | awk '{print $1}')"
	if [ "$actual" != "$expected" ]; then
		printf 'SHA-256 mismatch for %s: expected %s, got %s\n' "$path" "$expected" "$actual" >&2
		exit 1
	fi
}

normalize_hex_address() {
	local address="${1#0x}"
	printf '%016s' "$address" | tr ' ' 0
}

verify_symbol_bounds() {
	local binary="$1"
	local artifact_index="$2"
	local symbol_count
	local symbol_index=0
	symbol_count="$(jq ".artifacts[$artifact_index].required_symbols | length" "$manifest")"
	while [ "$symbol_index" -lt "$symbol_count" ]; do
		local symbol
		local expected_start
		local expected_end
		local expected_next
		local actual_start
		local next_record
		local actual_end
		local actual_next
		symbol="$(jq -r ".artifacts[$artifact_index].required_symbols[$symbol_index].name" "$manifest")"
		expected_start="$(normalize_hex_address "$(jq -r ".artifacts[$artifact_index].required_symbols[$symbol_index].start_vaddr" "$manifest")")"
		expected_end="$(normalize_hex_address "$(jq -r ".artifacts[$artifact_index].required_symbols[$symbol_index].symbol_interval_end_vaddr_exclusive" "$manifest")")"
		expected_next="$(jq -r ".artifacts[$artifact_index].required_symbols[$symbol_index].next_text_symbol" "$manifest")"
		actual_start="$(nm -n "$binary" | awk -v symbol="$symbol" '$2 ~ /^[Tt]$/ && $3 == symbol { print $1; exit }')"
		if [ "$actual_start" != "$expected_start" ]; then
			printf 'symbol start mismatch for %s in %s: expected %s, got %s\n' "$symbol" "$binary" "$expected_start" "${actual_start:-missing}" >&2
			exit 1
		fi
		next_record="$(nm -n "$binary" | awk -v symbol="$symbol" '$2 ~ /^[Tt]$/ && $3 == symbol { found=1; next } found && $2 ~ /^[Tt]$/ { print $1 " " $3; exit }')"
		actual_end="${next_record%% *}"
		actual_next="${next_record#* }"
		if [ "$actual_end" != "$expected_end" ] || [ "$actual_next" != "$expected_next" ]; then
			printf 'symbol interval mismatch for %s in %s: expected end/next %s %s, got %s %s\n' "$symbol" "$binary" "$expected_end" "$expected_next" "${actual_end:-missing}" "${actual_next:-missing}" >&2
			exit 1
		fi
		symbol_index=$((symbol_index + 1))
	done
}

artifact_count="$(jq '.artifacts | length' "$manifest")"
artifact_index=0
while [ "$artifact_index" -lt "$artifact_count" ]; do
	artifact_path="$(jq -r ".artifacts[$artifact_index].path" "$manifest")"
	artifact_sha="$(jq -r ".artifacts[$artifact_index].sha256" "$manifest")"
	source_path="$(jq -r ".artifacts[$artifact_index].source" "$manifest")"
	source_sha="$(jq -r ".artifacts[$artifact_index].source_sha256" "$manifest")"
	verify_hash "$repo_root/$artifact_path" "$artifact_sha"
	verify_hash "$repo_root/$source_path" "$source_sha"
	file "$repo_root/$artifact_path" | grep -F 'Mach-O 64-bit executable x86_64' >/dev/null
	verify_symbol_bounds "$repo_root/$artifact_path" "$artifact_index"
	otool -hv "$repo_root/$artifact_path" >"$output_dir/$(basename "$artifact_path").macho-header.txt"
	nm -n "$repo_root/$artifact_path" >"$output_dir/$(basename "$artifact_path").symbols.txt"
	artifact_index=$((artifact_index + 1))
done

capture_core_function() {
	local artifact="$1"
	local symbol="$2"
	local output="$3"
	R2_NOPLUGINS=1 "$r2_bin" -N -2q \
		-e scr.color=false -e log.level=0 -e bin.relocs.apply=true \
		-c "aaa; s sym.$symbol; pdfj" "$artifact" \
		| jq '{name,addr,size,bytes:([.ops[].bytes]|join("")),instructions:[.ops[]|{addr,size,bytes,opcode,type,jump,fail}|with_entries(select(.value != null))]}' \
		>"$output"
}

test_func="$repo_root/tests/r2r/bins/r2sleigh_test_func_x86_64_macho_O2_v1"
vuln_test="$repo_root/tests/r2r/bins/r2sleigh_vuln_test_x86_64_macho_O2_v1"
capture_core_function "$test_func" _sum_array "$output_dir/core/sum_array.json"
capture_core_function "$vuln_test" _check_secret "$output_dir/core/check_secret.json"
capture_core_function "$vuln_test" _complex_check "$output_dir/core/complex_check.json"
capture_core_function "$vuln_test" _test_struct_array_index "$output_dir/core/test_struct_array_index.json"

capture_sleigh_function() {
	local artifact="$1"
	local symbol="$2"
	local output="$3"
	R2_LIBR_PLUGINS="$R2SLEIGH_PLUGIN_DIR" "$r2_bin" -2q -a r2sleigh -b 64 \
		-e scr.color=false -e log.level=0 -e bin.relocs.apply=true \
		-c "a:sla >/dev/null; aaa; s sym.$symbol; af; a:sla.debug.ssa.func" "$artifact" \
		>"$output"
	[ -s "$output" ] && jq -e 'type == "object" and (.blocks | type == "array")' "$output" >/dev/null
}

if [ -n "${R2SLEIGH_PLUGIN_DIR:-}" ]; then
	set +e
	capture_sleigh_function "$test_func" _sum_array "$output_dir/sleigh/sum_array.json" 2>"$output_dir/sleigh/status.stderr"
	lift_status=$?
	if [ "$lift_status" -eq 0 ]; then
		capture_sleigh_function "$vuln_test" _check_secret "$output_dir/sleigh/check_secret.json" 2>>"$output_dir/sleigh/status.stderr"
		lift_status=$?
	fi
	if [ "$lift_status" -eq 0 ]; then
		capture_sleigh_function "$vuln_test" _complex_check "$output_dir/sleigh/complex_check.json" 2>>"$output_dir/sleigh/status.stderr"
		lift_status=$?
	fi
	if [ "$lift_status" -eq 0 ]; then
		capture_sleigh_function "$vuln_test" _test_struct_array_index "$output_dir/sleigh/test_struct_array_index.json" 2>>"$output_dir/sleigh/status.stderr"
		lift_status=$?
	fi
	set -e
	if [ "$lift_status" -eq 0 ]; then
		printf '{"status":"captured","plugin_dir":%s}\n' "$(printf '%s' "$R2SLEIGH_PLUGIN_DIR" | jq -Rs .)" >"$output_dir/sleigh/status.json"
	else
		printf '{"status":"unavailable","exit_status":%d,"reason":"configured plugin failed to load or capture"}\n' "$lift_status" >"$output_dir/sleigh/status.json"
	fi
else
	printf '%s\n' '{"status":"not_requested","reason":"set R2SLEIGH_PLUGIN_DIR to an ABI-compatible already-built plugin directory"}' >"$output_dir/sleigh/status.json"
fi

cp "$manifest" "$output_dir/manifest.json"
"$r2_bin" -v >"$output_dir/radare2-version.txt"
printf 'captured plain-O2 fixture metadata in %s\n' "$output_dir"
