# r2sleigh radare2 plugin Makefile

# Build configuration
RUST_TARGET ?= release
# Every architecture the plugin can lift. Building a subset is supported and
# occasionally useful, but it must be asked for: a default of x86 alone
# installs a plugin that answers "unknown architecture 'arm64'" on an ARM host,
# which reads as a missing backend rather than a build that left it out.
RUST_FEATURES ?= all-archs

# Paths
ANAL_PLUGIN_NAME = anal_sleigh
ARCH_PLUGIN_NAME = arch_sleigh
RUST_LIB = libr2sleigh_plugin
# Keep in sync with Cargo output directory. This allows CI to override
# CARGO_TARGET_DIR (e.g. shared incremental target on self-hosted runners).
CARGO_TARGET_DIR ?= ../target
RUST_BUILD_DIR = $(CARGO_TARGET_DIR)/$(RUST_TARGET)
RUST_RUNTIME_SUBDIR = r2sleigh
RUST_LIB_LOCAL = $(RUST_RUNTIME_SUBDIR)/$(RUST_LIB).$(RUST_LIB_EXT)
RUST_LINK_TARGET = $(abspath $(RUST_BUILD_DIR))/deps/$(RUST_LIB).$(RUST_LIB_EXT)
RUST_RUNTIME_REF = @loader_path/$(RUST_LIB_LOCAL)

ifeq ($(RUST_TARGET),release)
  RUST_CARGO_PROFILE_FLAG = --release
else ifeq ($(RUST_TARGET),debug)
  RUST_CARGO_PROFILE_FLAG =
else
  RUST_CARGO_PROFILE_FLAG = --profile $(RUST_TARGET)
endif

# Detect OS
UNAME := $(shell uname)
ifeq ($(UNAME),Darwin)
  RUST_LIB_EXT = dylib
  PLUGIN_EXT = dylib
  LDFLAGS_OS = -Wl,-rpath,@loader_path
else
  RUST_LIB_EXT = so
  PLUGIN_EXT = so
  LDFLAGS_OS = -Wl,-rpath,'$$ORIGIN' -Wl,-rpath,'$$ORIGIN/$(RUST_RUNTIME_SUBDIR)'
endif

# radare2 configuration
LOCAL_R2_DIR ?= ../../radare2
LOCAL_R2_ABS := $(abspath $(LOCAL_R2_DIR))
LOCAL_R2_INCLUDE := $(LOCAL_R2_ABS)/libr/include
LOCAL_R2_SDB_INCLUDE := $(LOCAL_R2_ABS)/subprojects/sdb/include
LOCAL_R2_ANAL_LIB := $(LOCAL_R2_ABS)/libr/anal/libr_anal.$(PLUGIN_EXT)
LOCAL_R2_LIB_FLAGS = \
	-L$(LOCAL_R2_ABS)/libr/core \
	-L$(LOCAL_R2_ABS)/libr/anal \
	-L$(LOCAL_R2_ABS)/libr/arch \
	-L$(LOCAL_R2_ABS)/libr/bin \
	-L$(LOCAL_R2_ABS)/libr/bp \
	-L$(LOCAL_R2_ABS)/libr/config \
	-L$(LOCAL_R2_ABS)/libr/debug \
	-L$(LOCAL_R2_ABS)/libr/util \
	-L$(LOCAL_R2_ABS)/libr/io \
	-L$(LOCAL_R2_ABS)/libr/reg \
	-L$(LOCAL_R2_ABS)/libr/esil \
	-L$(LOCAL_R2_ABS)/libr/cons \
	-L$(LOCAL_R2_ABS)/libr/flag \
	-L$(LOCAL_R2_ABS)/libr/search \
	-L$(LOCAL_R2_ABS)/libr/syscall \
	-L$(LOCAL_R2_ABS)/libr/muta \
	-lr_core -lr_anal -lr_arch -lr_bin -lr_bp -lr_config -lr_debug -lr_util -lr_io -lr_reg -lr_esil -lr_cons -lr_flag -lr_search -lr_syscall -lr_muta
ifeq ($(wildcard $(LOCAL_R2_INCLUDE)/r_anal.h)$(wildcard $(LOCAL_R2_ANAL_LIB)),)
R2_CFLAGS := $(shell pkg-config --cflags r_anal r_arch r_core 2>/dev/null || echo "-I/usr/include/libr")
R2_LDFLAGS := $(shell pkg-config --libs r_anal r_arch r_core 2>/dev/null || echo "-lr_core -lr_anal -lr_arch -lr_util -lr_io")
else
R2_CFLAGS := -I$(LOCAL_R2_INCLUDE) -I$(LOCAL_R2_SDB_INCLUDE)
R2_LDFLAGS := $(LOCAL_R2_LIB_FLAGS)
endif
R2_PLUGIN_DIR := $(shell r2 -H R2_USER_PLUGINS 2>/dev/null || echo "$(HOME)/.local/share/radare2/plugins")

# Compiler settings
CC ?= gcc
CFLAGS_OBJ = -Wall -Wextra -fPIC $(R2_CFLAGS)
CFLAGS_SO = -Wall -Wextra -fPIC -shared $(R2_CFLAGS)
LDFLAGS = $(R2_LDFLAGS) -L$(RUST_BUILD_DIR) -lr2sleigh_plugin $(LDFLAGS_OS) -lstdc++

# Output
ANAL_PLUGIN_SO = $(ANAL_PLUGIN_NAME).$(PLUGIN_EXT)
ARCH_PLUGIN_SO = $(ARCH_PLUGIN_NAME).$(PLUGIN_EXT)

.PHONY: all clean install uninstall rust rust-debug rust-release rust-dist ffi-v2-conformance help arch_sleigh.o r_anal_sleigh_arch.o fixup-dylibs FORCE

RUST_MANIFESTS := ../Cargo.toml $(wildcard ../.cargo/config.toml ../crates/*/Cargo.toml ../r2plugin/Cargo.toml)
RUST_SOURCES := $(shell find ../r2plugin/src ../crates -type f -name '*.rs')
RUST_BUILD_PREREQS := $(RUST_MANIFESTS) $(RUST_SOURCES)

all: $(RUST_LIB_LOCAL) $(ANAL_PLUGIN_SO) $(ARCH_PLUGIN_SO)

# Build the analysis plugin shared object
$(ANAL_PLUGIN_SO): r_anal_sleigh.c snapshot_wire.c snapshot_walk.c snapshot_capture.c snapshot_wire.h snapshot_capture.h $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)
	$(CC) $(CFLAGS_SO) -o $@ r_anal_sleigh.c snapshot_wire.c snapshot_walk.c snapshot_capture.c $(LDFLAGS)
ifeq ($(UNAME),Darwin)
	@for from in "$(RUST_LINK_TARGET)" "@loader_path/$(RUST_LIB).$(RUST_LIB_EXT)"; do \
		if otool -L $@ | grep -Fq "$$from"; then \
			install_name_tool -change "$$from" "$(RUST_RUNTIME_REF)" $@; \
		fi; \
	done
	@codesign --force --sign - $@ >/dev/null
endif

# Build the architecture plugin shared object
ARCH_PLUGIN_OBJS = arch_sleigh.o r_anal_sleigh_arch.o snapshot_wire.o snapshot_walk.o snapshot_capture.o

snapshot_wire.o: snapshot_wire.c snapshot_wire.h
	$(CC) $(CFLAGS_OBJ) -c -o $@ $<

snapshot_walk.o: snapshot_walk.c snapshot_wire.h snapshot_capture.h
	$(CC) $(CFLAGS_OBJ) -c -o $@ $<

snapshot_capture.o: snapshot_capture.c snapshot_capture.h
	$(CC) $(CFLAGS_OBJ) -c -o $@ $<

arch_sleigh.o: arch_sleigh.c
	$(CC) $(CFLAGS_OBJ) -c -o $@ $<

r_anal_sleigh_arch.o: r_anal_sleigh.c
	$(CC) $(CFLAGS_OBJ) -DR2_PLUGIN_INCORE -c -o $@ $<

$(ARCH_PLUGIN_SO): $(ARCH_PLUGIN_OBJS) $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)
	$(CC) $(CFLAGS_SO) -o $@ $(ARCH_PLUGIN_OBJS) $(LDFLAGS)
ifeq ($(UNAME),Darwin)
	@for from in "$(RUST_LINK_TARGET)" "@loader_path/$(RUST_LIB).$(RUST_LIB_EXT)"; do \
		if otool -L $@ | grep -Fq "$$from"; then \
			install_name_tool -change "$$from" "$(RUST_RUNTIME_REF)" $@; \
		fi; \
	done
	@codesign --force --sign - $@ >/dev/null
endif

# Default rust target
rust: $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)
rust-debug:
	$(MAKE) rust RUST_TARGET=debug RUST_FEATURES=$(RUST_FEATURES)
rust-release:
	$(MAKE) rust RUST_TARGET=release RUST_FEATURES=$(RUST_FEATURES)
rust-dist:
	$(MAKE) rust RUST_TARGET=dist RUST_FEATURES=$(RUST_FEATURES)

$(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT): FORCE $(RUST_BUILD_PREREQS)
	cd .. && cargo build $(RUST_CARGO_PROFILE_FLAG) --features $(RUST_FEATURES) -p r2sleigh-plugin
ifeq ($(UNAME),Darwin)
	@desired='@loader_path/$(RUST_LIB).$(RUST_LIB_EXT)'; \
	current="$$(otool -D "$(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)" 2>/dev/null | tail -n 1)"; \
	if [ "$$current" != "$$desired" ]; then \
		install_name_tool -id "$$desired" "$(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)"; \
	fi; \
	if ! codesign -v "$(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)" >/dev/null 2>&1; then \
		codesign --force --sign - "$(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)" >/dev/null 2>&1; \
	fi
endif

$(RUST_LIB_LOCAL): FORCE $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)
	mkdir -p $(RUST_RUNTIME_SUBDIR)
	@if [ "$(UNAME)" != Darwin ] && [ -f "$@" ] \
		&& cmp -s "$(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)" "$@"; then \
		exit 0; \
	fi; \
	rust_lib_tmp_dir="$$(mktemp -d "$(RUST_RUNTIME_SUBDIR)/.r2sleigh-runtime.XXXXXX")" || exit 1; \
	rust_lib_tmp="$$rust_lib_tmp_dir/$(RUST_LIB).$(RUST_LIB_EXT)"; \
	cleanup_rust_lib_tmp () { \
		rm -f "$$rust_lib_tmp"; \
		rmdir "$$rust_lib_tmp_dir" >/dev/null 2>&1 || true; \
	}; \
	trap cleanup_rust_lib_tmp EXIT; \
	trap 'exit 1' HUP INT TERM; \
	cp "$(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)" "$$rust_lib_tmp" || exit 1; \
	if [ "$(UNAME)" = Darwin ]; then \
		codesign --force --sign - "$$rust_lib_tmp" >/dev/null 2>&1 || exit 1; \
	fi; \
	mv -f "$$rust_lib_tmp" "$@" || exit 1; \
	rmdir "$$rust_lib_tmp_dir" || exit 1; \
	trap - EXIT HUP INT TERM

FFI_V2_CONFORMANCE_BIN = $(RUST_BUILD_DIR)/ffi_v2_header_conformance

ffi-v2-conformance: $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT) tests/ffi_v2_header_conformance.c tests/ffi_v2_symbol_absence.sh r2sleigh_api_v2.h
	$(CC) -Wall -Wextra -I. -o $(FFI_V2_CONFORMANCE_BIN) tests/ffi_v2_header_conformance.c \
		-L$(RUST_BUILD_DIR) -lr2sleigh_plugin $(LDFLAGS_OS)
	$(FFI_V2_CONFORMANCE_BIN)
	sh tests/ffi_v2_symbol_absence.sh $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)

SNAPSHOT_WIRE_CONFORMANCE_BIN = $(RUST_BUILD_DIR)/snapshot_wire_conformance

# The C writer must stay byte-identical to r2source::snapshot_wire. Both sides
# pin the same vector, so drift in either fails a test.
snapshot-wire-conformance: tests/snapshot_wire_conformance.c snapshot_wire.c snapshot_wire.h
	@mkdir -p $(RUST_BUILD_DIR)
	$(CC) -Wall -Wextra -I. -o $(SNAPSHOT_WIRE_CONFORMANCE_BIN) \
		tests/snapshot_wire_conformance.c snapshot_wire.c
	$(SNAPSHOT_WIRE_CONFORMANCE_BIN)

# Install plugins
install: $(RUST_LIB_LOCAL) $(ANAL_PLUGIN_SO) $(ARCH_PLUGIN_SO)
	@mkdir -p $(R2_PLUGIN_DIR)
	@mkdir -p $(R2_PLUGIN_DIR)/$(RUST_RUNTIME_SUBDIR)
	rm -f $(R2_PLUGIN_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)
	cp $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT) $(R2_PLUGIN_DIR)/$(RUST_RUNTIME_SUBDIR)/
	cp $(ANAL_PLUGIN_SO) $(R2_PLUGIN_DIR)/
	cp $(ARCH_PLUGIN_SO) $(R2_PLUGIN_DIR)/
ifeq ($(UNAME),Darwin)
	@codesign --force --sign - $(R2_PLUGIN_DIR)/$(RUST_RUNTIME_SUBDIR)/$(RUST_LIB).$(RUST_LIB_EXT) >/dev/null
	@codesign --force --sign - $(R2_PLUGIN_DIR)/$(ANAL_PLUGIN_SO) >/dev/null
	@codesign --force --sign - $(R2_PLUGIN_DIR)/$(ARCH_PLUGIN_SO) >/dev/null
endif
	@echo "Installed to $(R2_PLUGIN_DIR)"

# Uninstall plugins
uninstall:
	rm -f $(R2_PLUGIN_DIR)/$(ANAL_PLUGIN_SO)
	rm -f $(R2_PLUGIN_DIR)/$(ARCH_PLUGIN_SO)
	rm -f $(R2_PLUGIN_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)
	rm -f $(R2_PLUGIN_DIR)/$(RUST_RUNTIME_SUBDIR)/$(RUST_LIB).$(RUST_LIB_EXT)
	@echo "Uninstalled from $(R2_PLUGIN_DIR)"

# Clean build artifacts
clean:
	rm -f $(ANAL_PLUGIN_SO) $(ARCH_PLUGIN_SO) $(ARCH_PLUGIN_OBJS)
	rm -f $(RUST_LIB).$(RUST_LIB_EXT)
	rm -rf $(RUST_RUNTIME_SUBDIR)

# Full clean including Rust
distclean: clean
	cd .. && cargo clean

# Help
help:
	@echo "r2sleigh radare2 plugin build"
	@echo ""
	@echo "Targets:"
	@echo "  all          - Build both analysis and architecture plugins (default)"
	@echo "  rust         - Build only the Rust library"
	@echo "  install      - Install plugins to radare2 plugins dir"
	@echo "  uninstall    - Remove plugins from radare2 plugins dir"
	@echo "  clean        - Remove build artifacts"
	@echo "  distclean    - Remove all build artifacts including Rust"
	@echo ""
	@echo "Variables:"
	@echo "  RUST_TARGET   - 'release' (default) or 'debug'"
	@echo "                  use 'dist' for fat-LTO distributable artifacts"
	@echo "  RUST_FEATURES - Sleigh features: 'all-archs' (default), 'x86', 'arm' (ARM32 + AArch64), 'mips', 'riscv'"
	@echo ""
	@echo "Examples:"
	@echo "  make                           # Build release with x86"
	@echo "  make RUST_FEATURES=all-archs   # Build with all architectures"
	@echo "  make RUST_TARGET=debug         # Build debug version"
	@echo "  make RUST_TARGET=dist          # Build maximum-optimized release"
	@echo "  make install                   # Install to r2 plugins"
