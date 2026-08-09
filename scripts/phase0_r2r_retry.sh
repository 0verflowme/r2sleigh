#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
baseline_root="/tmp/r2sleigh-phase0-baseline-0cbe057e"
radare2_root="/tmp/radare2-phase0-62791dc5"
radare2_bin="$radare2_root/binr/radare2/radare2"
plugin_dir="/tmp/r2sleigh-phase0-baseline-plugins-v2"
archive="$repo_root/target/phase0-baseline-v2-0cbe057e-62791dc5"

test -d "$archive"
test -x "$radare2_bin"
test -f "$plugin_dir/r2sleigh/libr2sleigh_plugin.dylib"
test "$(git -C "$baseline_root" rev-parse HEAD)" = "0cbe057efb8427b021e1c8cde4d721573fdb9fdd"
test "$(git -C "$radare2_root" rev-parse HEAD)" = "62791dc54f6af6e95d9a61c997e5c1eda098775d"
test -z "$(git -C "$baseline_root" status --porcelain=v1)"
test -z "$(git -C "$radare2_root" status --porcelain=v1)"
cmp -s "$radare2_bin" "$archive/artifacts/radare2"
cmp -s "$plugin_dir/anal_sleigh.dylib" "$archive/artifacts/anal_sleigh.dylib"
cmp -s "$plugin_dir/arch_sleigh.dylib" "$archive/artifacts/arch_sleigh.dylib"
cmp -s "$plugin_dir/r2sleigh/libr2sleigh_plugin.dylib" \
	"$archive/artifacts/libr2sleigh_plugin.dylib"
mkdir -p "$archive/r2r-logs-v2"
cp "${BASH_SOURCE[0]}" "$archive/executed-r2r-retry-script.sh"
cp "$archive/SHA256SUMS" "$archive/SHA256SUMS.initial"
exec >"$archive/r2r-retry-execution.log" 2>&1
PS4='+ ${BASH_SOURCE}:${LINENO}: '
set -x

radare2_library_path="$(find "$radare2_root/libr" -mindepth 1 -maxdepth 1 -type d | sort | paste -sd: -)"
run_r2r() {
	local id="$1"
	local database="$2"
	local r2r_tmp
	r2r_tmp="$(mktemp -d "/tmp/phase0-v2-retry-${id}.XXXXXX")"
	set +e
	env \
		TMPDIR="$r2r_tmp" TMP="$r2r_tmp" TEMP="$r2r_tmp" \
		XDG_DATA_HOME="$r2r_tmp/xdg-data" \
		R2R_RADARE2="$radare2_bin" \
		R2_LIBR_PLUGINS="$plugin_dir" \
		LD_LIBRARY_PATH="$radare2_library_path${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
		DYLD_LIBRARY_PATH="$radare2_library_path${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}" \
		r2r -t 120 -j 1 -L "$database" >"$archive/r2r-logs-v2/$id.log" 2>&1
	local status=$?
	set -e
	printf '%s\t%s\n' "$id" "$status" >>"$archive/r2r-retry-status.tsv"
}

run_r2r r2r-full-extras "$baseline_root/tests/r2r/db/extras"
run_r2r r2r-fast "$baseline_root/tests/r2r/db/extras/r2sleigh_integration_fast"
run_r2r r2r-extended "$baseline_root/tests/r2r/db/extras/r2sleigh_integration_extended"
run_r2r r2r-decompiler-snapshots "$baseline_root/tests/r2r/db/extras/r2sleigh_decompiler_snapshots"

set +x
exec 1>&- 2>&-
(
	cd "$archive"
	find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 shasum -a 256
) >"$archive/SHA256SUMS"
