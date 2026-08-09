#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
baseline_root="/tmp/r2sleigh-phase0-baseline-0cbe057e"
radare2_root="/tmp/radare2-phase0-62791dc5"
radare2_bin="$radare2_root/binr/radare2/radare2"
plugin_dir="/tmp/r2sleigh-phase0-baseline-plugins-v2"
archive="$repo_root/target/phase0-baseline-v2-0cbe057e-62791dc5"
capture_started_at_utc="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"

if [[ -e "$archive" ]]; then
	printf 'refusing to overwrite existing archive: %s\n' "$archive" >&2
	exit 1
fi

test "$(git -C "$baseline_root" rev-parse HEAD)" = "0cbe057efb8427b021e1c8cde4d721573fdb9fdd"
test "$(git -C "$radare2_root" rev-parse HEAD)" = "62791dc54f6af6e95d9a61c997e5c1eda098775d"
test -z "$(git -C "$baseline_root" status --porcelain=v1)"
test -z "$(git -C "$radare2_root" status --porcelain=v1)"
test -x "$radare2_bin"
test -f "$plugin_dir/r2sleigh/libr2sleigh_plugin.dylib"
test -f /tmp/radare2-phase0-62791dc5-build-verification.log
test -f /tmp/r2sleigh-phase0-0cbe057e-plugin-build-verification.log

mkdir -p "$archive/reports" "$archive/raw" "$archive/r2r-logs" "$archive/artifacts"
cp "${BASH_SOURCE[0]}" "$archive/executed-capture-script.sh"
exec >"$archive/execution.log" 2>&1
PS4='+ ${BASH_SOURCE}:${LINENO}: '
set -x

printf '%s\n' \
	"repo_root=$repo_root" \
	"baseline_root=$baseline_root" \
	"radare2_root=$radare2_root" \
	"radare2_bin=$radare2_bin" \
	"plugin_dir=$plugin_dir" \
	"archive=$archive" \
	"r2sleigh_commit=$(git -C "$baseline_root" rev-parse HEAD)" \
	"radare2_commit=$(git -C "$radare2_root" rev-parse HEAD)" \
	"capture_started_at_utc=$capture_started_at_utc" \
	"script_sha256=$(shasum -a 256 "${BASH_SOURCE[0]}" | awk '{print $1}')" \
	>"$archive/provenance.env"

radare2_library_path="$(find "$radare2_root/libr" -mindepth 1 -maxdepth 1 -type d | sort | paste -sd: -)"
export LD_LIBRARY_PATH="$radare2_library_path${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export DYLD_LIBRARY_PATH="$radare2_library_path${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"

git -C "$baseline_root" status --porcelain=v1 >"$archive/r2sleigh-status.txt"
git -C "$radare2_root" status --porcelain=v1 >"$archive/radare2-status.txt"
"$radare2_bin" -V >"$archive/radare2-version.txt" 2>&1
python3 --version >"$archive/tool-versions.txt" 2>&1
rustc --version >>"$archive/tool-versions.txt" 2>&1
cargo --version >>"$archive/tool-versions.txt" 2>&1
r2r -v >>"$archive/tool-versions.txt" 2>&1
uname -sr >>"$archive/tool-versions.txt" 2>&1
uname -m >>"$archive/tool-versions.txt" 2>&1
clang --version >>"$archive/tool-versions.txt" 2>&1
cp "$radare2_bin" "$archive/artifacts/radare2"
cp "$plugin_dir/anal_sleigh.dylib" "$archive/artifacts/anal_sleigh.dylib"
cp "$plugin_dir/arch_sleigh.dylib" "$archive/artifacts/arch_sleigh.dylib"
cp "$plugin_dir/r2sleigh/libr2sleigh_plugin.dylib" "$archive/artifacts/libr2sleigh_plugin.dylib"
cp "$baseline_root/tests/e2e/vuln_test_x86" "$archive/artifacts/vuln_test_x86"
cp "$baseline_root/tests/e2e/test_func_x86" "$archive/artifacts/test_func_x86"
cp "$baseline_root/tests/r2r/bins/r2sleigh_manual_limits_O0" "$archive/artifacts/r2sleigh_manual_limits_O0"
cp "$baseline_root/tests/r2r/bins/r2sleigh_manual_limits_O2" "$archive/artifacts/r2sleigh_manual_limits_O2"
cp -L "$baseline_root/tests/r2r/bins/stress_test_x86" \
	"$archive/artifacts/source_gold_stress_test_x86"
cp -L "$baseline_root/tests/r2r/bins/vuln_test_x86" \
	"$archive/artifacts/source_gold_vuln_test_x86"
cp "$baseline_root/tests/r2r/bins/r2sleigh_manual_limits_O0" \
	"$archive/artifacts/source_gold_r2sleigh_manual_limits_O0"
cp "$baseline_root/tests/r2r/bins/r2sleigh_manual_limits_O2" \
	"$archive/artifacts/source_gold_r2sleigh_manual_limits_O2"
cp "$repo_root/scripts/reversing_benchmark.py" "$archive/executed-reversing-benchmark.py"
cp "$repo_root/tests/gold/source_oracle.json" "$archive/executed-source-oracle.json"
jq --arg artifact_root "$archive/artifacts" '
	.binaries |= map(
		.path = ($artifact_root + "/source_gold_" + (.path | split("/") | last))
	)
' "$repo_root/tests/gold/closure_manifest.json" \
	>"$archive/executed-closure-manifest.json"
cp /tmp/radare2-phase0-62791dc5-build-verification.log \
	"$archive/radare2-build-verification.log"
cp /tmp/r2sleigh-phase0-0cbe057e-plugin-build-verification.log \
	"$archive/r2sleigh-plugin-build-verification.log"

run_benchmark() {
	local id="$1"
	local binary="$2"
	local temperature="$3"
	shift 3
	local bench_tmp
	bench_tmp="$(mktemp -d "/tmp/phase0-v2-${id}.XXXXXX")"
	local args=(
		python3 "$repo_root/scripts/reversing_benchmark.py"
		--r2 "$radare2_bin"
		--plugin-dir "$plugin_dir"
		--manifest-only
		--binary "$binary"
		--analysis aaa
		--commands decompile_sla,types,profile
		--include-sensitive
		--tmpdir "$bench_tmp"
		--raw-output-dir "$archive/raw/$id"
		--out "$archive/reports/$id.json"
	)
	local target
	for target in "$@"; do
		args+=(--target "$target")
	done
	if [[ "$temperature" = cold ]]; then
		args+=(--isolate-commands --repeat 1)
	else
		args+=(--repeat 2 --cache-probe)
	fi
	"${args[@]}"
}

run_benchmark vuln-cold "$baseline_root/tests/e2e/vuln_test_x86" cold \
	check_secret complex_check test_struct_array_index process_string authenticate alloc_and_copy
run_benchmark vuln-warm "$baseline_root/tests/e2e/vuln_test_x86" warm \
	check_secret complex_check test_struct_array_index process_string authenticate alloc_and_copy
run_benchmark test-func-cold "$baseline_root/tests/e2e/test_func_x86" cold \
	sum_array alloc_wrapper alloc_wrapper2 memcpy_wrapper
run_benchmark test-func-warm "$baseline_root/tests/e2e/test_func_x86" warm \
	sum_array alloc_wrapper alloc_wrapper2 memcpy_wrapper
run_benchmark manual-o0-cold "$baseline_root/tests/r2r/bins/r2sleigh_manual_limits_O0" cold \
	struct_nested_array fnv_fold sparse_switch state_machine mem_scan2
run_benchmark manual-o0-warm "$baseline_root/tests/r2r/bins/r2sleigh_manual_limits_O0" warm \
	struct_nested_array fnv_fold sparse_switch state_machine mem_scan2
run_benchmark manual-o2-cold "$baseline_root/tests/r2r/bins/r2sleigh_manual_limits_O2" cold \
	struct_nested_array fnv_fold sparse_switch state_machine mem_scan2
run_benchmark manual-o2-warm "$baseline_root/tests/r2r/bins/r2sleigh_manual_limits_O2" warm \
	struct_nested_array fnv_fold sparse_switch state_machine mem_scan2

source_gold_tmp="$(mktemp -d /tmp/phase0-v2-source-gold.XXXXXX)"
set +e
python3 "$repo_root/scripts/reversing_benchmark.py" \
	--manifest "$archive/executed-closure-manifest.json" \
	--gold-manifest "$repo_root/tests/gold/source_oracle.json" \
	--manifest-only \
	--closure-gate \
	--commands decompile_sla,decompile_pdd,types,profile \
	--analysis aaa \
	--timeout 120 \
	--jobs 1 \
	--plugin-dir "$plugin_dir" \
	--r2 "$radare2_bin" \
	--tmpdir "$source_gold_tmp/bench" \
	--raw-output-dir "$archive/raw/source-gold" \
	--include-sensitive \
	--out "$archive/reports/source-gold.json"
source_gold_status=$?
set -e
printf 'source-gold\t%s\n' "$source_gold_status" >"$archive/command-status.tsv"

run_r2r() {
	local id="$1"
	local database="$2"
	local r2r_tmp
	r2r_tmp="$(mktemp -d "/tmp/phase0-v2-${id}.XXXXXX")"
	set +e
	env \
		TMPDIR="$r2r_tmp" TMP="$r2r_tmp" TEMP="$r2r_tmp" \
		XDG_DATA_HOME="$r2r_tmp/xdg-data" \
		R2R_RADARE2="$radare2_bin" \
		R2_LIBR_PLUGINS="$plugin_dir" \
		LD_LIBRARY_PATH="$radare2_library_path${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
		DYLD_LIBRARY_PATH="$radare2_library_path${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}" \
		r2r -t 120 -j 1 -L "$database" >"$archive/r2r-logs/$id.log" 2>&1
	local status=$?
	set -e
	printf '%s\t%s\n' "$id" "$status" >>"$archive/command-status.tsv"
}

run_r2r r2r-full-extras "$baseline_root/tests/r2r/db/extras"
run_r2r r2r-fast "$baseline_root/tests/r2r/db/extras/r2sleigh_integration_fast"
run_r2r r2r-extended "$baseline_root/tests/r2r/db/extras/r2sleigh_integration_extended"
run_r2r r2r-decompiler-snapshots "$baseline_root/tests/r2r/db/extras/r2sleigh_decompiler_snapshots"

set +x
date -u '+%Y-%m-%dT%H:%M:%SZ' >"$archive/evidence-collection-finished-at-utc.txt"
exec 1>&- 2>&-
(
	cd "$archive"
	find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 shasum -a 256
) >"$archive/SHA256SUMS"
