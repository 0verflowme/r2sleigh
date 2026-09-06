#!/bin/bash
# Build each project once per (architecture, optimisation, linkage) and keep it twice.
#
# The stripped binary is a copy of the one that kept its debug info, so the two
# describe the same machine code exactly. Building twice would risk different
# codegen and make the difference between them something other than the debug
# info, which is the one thing the scoring must isolate.
#
# Static linkage is built as well as dynamic because that is where library code
# stops being an import and becomes anonymous code in the binary.
set -uo pipefail

OUT=${OUT:-/out}
JOBS=${JOBS:-4}
ARCHES=${ARCHES:-"x86_64 aarch64"}
OPTS=${OPTS:-"-O0 -O2"}
LINKAGES=${LINKAGES:-"dynamic static"}

fetch() {
	local url=$1 dir=$2 flag=$3
	[ -f "$dir/.fetched" ] && return 0
	mkdir -p "$dir"
	curl -fsSL "$url" | tar "-x${flag}" -C "$dir" --strip-components=1 || return 1
	touch "$dir/.fetched"
}

keep() {
	local built=$1 name=$2 arch=$3 opt=$4 link=$5
	local dest="$OUT/$arch/${opt#-}-$link"
	mkdir -p "$dest" || return 1
	cp "$built" "$dest/$name.debug" || return 1
	cp "$built" "$dest/$name" || return 1
	"$STRIP" --strip-all "$dest/$name" || return 1
	printf '  built %-18s %s %s %s\n' "$name" "$arch" "$opt" "$link"
}

link_flag() { [ "$1" = static ] && echo -static || echo; }

build_zlib() {
	local arch=$1 opt=$2 link=$3
	fetch https://zlib.net/fossils/zlib-1.3.1.tar.gz /src/zlib z || return 1
	local b=/tmp/zlib-$arch$opt-$link
	rm -rf "$b" && cp -r /src/zlib "$b" && cd "$b" || return 1
	make -f win32/Makefile.msc distclean >/dev/null 2>&1
	rm -f *.o *.a
	for c in adler32 crc32 deflate infback inffast inflate inftrees trees zutil \
		compress uncompr gzclose gzlib gzread gzwrite; do
		"$CC" $opt -g -c -I. "$c.c" -o "$c.o" || return 1
	done
	"$AR" rcs libz.a ./*.o || return 1
	"$CC" $opt -g $(link_flag "$link") -o minigzip test/minigzip.c libz.a -I. || return 1
	keep "$b/minigzip" zlib-minigzip "$arch" "$opt" "$link"
}

build_sqlite() {
	local arch=$1 opt=$2 link=$3
	fetch https://www.sqlite.org/2024/sqlite-autoconf-3450100.tar.gz /src/sqlite z || return 1
	local b=/tmp/sqlite-$arch$opt-$link
	rm -rf "$b" && mkdir -p "$b" && cd "$b" || return 1
	"$CC" $opt -g $(link_flag "$link") -o sqlite3 \
		/src/sqlite/shell.c /src/sqlite/sqlite3.c -I/src/sqlite \
		-DSQLITE_THREADSAFE=0 -DSQLITE_OMIT_LOAD_EXTENSION -lm || return 1
	keep "$b/sqlite3" sqlite3 "$arch" "$opt" "$link"
}

build_busybox() {
	local arch=$1 opt=$2 link=$3
	fetch https://busybox.net/downloads/busybox-1.36.1.tar.bz2 /src/busybox j || return 1
	local b=/tmp/busybox-$arch$opt-$link
	rm -rf "$b" && cp -r /src/busybox "$b" && cd "$b" || return 1
	make defconfig >/dev/null 2>&1 || return 1
	# busybox strips its own output, and the unstripped copy is the truth
	sed -i 's/^CONFIG_STATIC=.*/CONFIG_STATIC=y/' .config
	[ "$link" = static ] || sed -i 's/^CONFIG_STATIC=.*/# CONFIG_STATIC is not set/' .config
	yes '' | make oldconfig >/dev/null 2>&1
	make -j"$JOBS" CC="$CC" STRIP="$STRIP" \
		CONFIG_EXTRA_CFLAGS="$opt -g" >/dev/null 2>&1
	local out=busybox_unstripped
	[ -f "$out" ] || out=busybox
	[ -f "$out" ] || return 1
	keep "$b/$out" busybox "$arch" "$opt" "$link"
}

for arch in $ARCHES; do
	case $arch in
	x86_64)  CC=x86_64-linux-gnu-gcc;  STRIP=x86_64-linux-gnu-strip;  AR=x86_64-linux-gnu-ar ;;
	aarch64) CC=aarch64-linux-gnu-gcc; STRIP=aarch64-linux-gnu-strip; AR=aarch64-linux-gnu-ar ;;
	*) echo "unknown arch $arch" >&2; exit 1 ;;
	esac
	export CC STRIP AR
	for opt in $OPTS; do
		for link in $LINKAGES; do
			for p in ${PROJECTS:-zlib sqlite busybox}; do
				"build_$p" "$arch" "$opt" "$link" || echo "  FAILED $p $arch $opt $link" >&2
			done
		done
	done
done

echo
echo "corpus:"
find "$OUT" -type f ! -name '*.debug' | sort | sed "s|^$OUT/|  |"
