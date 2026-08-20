#!/bin/bash
# Build each project once per (architecture, optimisation) and keep it twice.
#
# The stripped binary is a copy of the one that kept its debug info, so the two
# describe the same machine code exactly. Building twice would risk different
# codegen and make the difference between them something other than the debug
# info, which is the one thing the scoring must isolate.
set -euo pipefail

OUT=${OUT:-/out}
JOBS=${JOBS:-4}
ARCHES=${ARCHES:-"x86_64 aarch64"}
OPTS=${OPTS:-"-O0 -O2"}

fetch() {
	local url=$1 dir=$2
	[ -d "$dir" ] && return 0
	mkdir -p "$dir"
	curl -fsSL "$url" | tar -xz -C "$dir" --strip-components=1
}

keep() {
	# keep <built-binary> <name> <arch> <opt>
	local built=$1 name=$2 arch=$3 opt=$4
	local dest="$OUT/$arch/${opt#-}"
	mkdir -p "$dest"
	cp "$built" "$dest/$name.debug"
	cp "$built" "$dest/$name"
	"${STRIP}" --strip-all "$dest/$name"
	printf '  %-12s %s %s\n' "$name" "$arch" "$opt"
}

build_zlib() {
	local arch=$1 opt=$2
	fetch https://zlib.net/fossils/zlib-1.3.1.tar.gz /src/zlib
	local b=/tmp/zlib-$arch-$opt
	rm -rf "$b"; cp -r /src/zlib "$b"; cd "$b"
	CC="$CC" CFLAGS="$opt -g -fno-omit-frame-pointer" ./configure --static >/dev/null
	make -j"$JOBS" >/dev/null 2>&1
	# minigzip links the whole library and is a real program rather than a stub
	"$CC" $opt -g -o minigzip test/minigzip.c libz.a -I. >/dev/null 2>&1
	keep "$b/minigzip" zlib-minigzip "$arch" "$opt"
}

build_sqlite() {
	local arch=$1 opt=$2
	fetch https://www.sqlite.org/2024/sqlite-autoconf-3450100.tar.gz /src/sqlite
	local b=/tmp/sqlite-$arch-$opt
	rm -rf "$b"; mkdir -p "$b"; cd "$b"
	"$CC" $opt -g -fno-omit-frame-pointer -o sqlite3 \
		/src/sqlite/shell.c /src/sqlite/sqlite3.c \
		-I/src/sqlite -DSQLITE_THREADSAFE=0 -DSQLITE_OMIT_LOAD_EXTENSION \
		-lm >/dev/null 2>&1
	keep "$b/sqlite3" sqlite3 "$arch" "$opt"
}

build_busybox() {
	local arch=$1 opt=$2
	fetch https://busybox.net/downloads/busybox-1.36.1.tar.bz2 /src/busybox || true
	if [ ! -f /src/busybox/Makefile ]; then
		mkdir -p /src/busybox
		curl -fsSL https://busybox.net/downloads/busybox-1.36.1.tar.bz2 \
			| tar -xj -C /src/busybox --strip-components=1
	fi
	local b=/tmp/busybox-$arch-$opt
	rm -rf "$b"; cp -r /src/busybox "$b"; cd "$b"
	make defconfig >/dev/null 2>&1
	sed -i 's/^CONFIG_DEBUG.*/# unset/' .config
	make -j"$JOBS" CC="$CC" CFLAGS_EXTRA="$opt -g" busybox >/dev/null 2>&1
	keep "$b/busybox_unstripped" busybox "$arch" "$opt"
}

build_coreutils() {
	local arch=$1 opt=$2
	fetch https://ftp.gnu.org/gnu/coreutils/coreutils-9.4.tar.xz /src/coreutils || {
		mkdir -p /src/coreutils
		curl -fsSL https://ftp.gnu.org/gnu/coreutils/coreutils-9.4.tar.xz \
			| tar -xJ -C /src/coreutils --strip-components=1
	}
	local b=/tmp/coreutils-$arch-$opt
	rm -rf "$b"; mkdir -p "$b"; cd "$b"
	/src/coreutils/configure --host="$HOST" CC="$CC" \
		CFLAGS="$opt -g -fno-omit-frame-pointer" >/dev/null 2>&1
	make -j"$JOBS" >/dev/null 2>&1 || true
	for tool in ls cp sort; do
		[ -f "src/$tool" ] && keep "src/$tool" "coreutils-$tool" "$arch" "$opt"
	done
}

for arch in $ARCHES; do
	case $arch in
	x86_64)  CC=x86_64-linux-gnu-gcc;  STRIP=x86_64-linux-gnu-strip;  HOST=x86_64-linux-gnu ;;
	aarch64) CC=aarch64-linux-gnu-gcc; STRIP=aarch64-linux-gnu-strip; HOST=aarch64-linux-gnu ;;
	*) echo "unknown arch $arch" >&2; exit 1 ;;
	esac
	export CC STRIP HOST
	for opt in $OPTS; do
		echo "== $arch $opt =="
		for project in "${PROJECTS:-zlib sqlite busybox coreutils}"; do
			for p in $project; do
				"build_$p" "$arch" "$opt" || echo "  $p FAILED" >&2
			done
		done
	done
done

echo
echo "corpus:"
find "$OUT" -type f ! -name '*.debug' | sort | while read -r f; do
	printf '  %s\n' "${f#$OUT/}"
done
