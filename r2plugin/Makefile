# r2sleigh radare2 plugin Makefile

# Build configuration
RUST_TARGET ?= release
RUST_FEATURES ?= x86

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
R2_CFLAGS := $(shell pkg-config --cflags r_anal r_arch r_core 2>/dev/null || echo "-I/usr/include/libr")
R2_LDFLAGS := $(shell pkg-config --libs r_anal r_arch r_core 2>/dev/null || echo "-lr_core -lr_anal -lr_arch -lr_util -lr_io")
R2_PLUGIN_DIR := $(shell r2 -H R2_USER_PLUGINS 2>/dev/null || echo "$(HOME)/.local/share/radare2/plugins")

# Compiler settings
CC ?= gcc
CFLAGS_OBJ = -Wall -Wextra -fPIC $(R2_CFLAGS)
CFLAGS_SO = -Wall -Wextra -fPIC -shared $(R2_CFLAGS)
LDFLAGS = $(R2_LDFLAGS) -L$(RUST_BUILD_DIR) -lr2sleigh_plugin $(LDFLAGS_OS) -lstdc++

# Output
ANAL_PLUGIN_SO = $(ANAL_PLUGIN_NAME).$(PLUGIN_EXT)
ARCH_PLUGIN_SO = $(ARCH_PLUGIN_NAME).$(PLUGIN_EXT)

.PHONY: all clean install uninstall rust rust-debug rust-release help arch_sleigh.o r_anal_sleigh_arch.o fixup-dylibs

all: $(RUST_LIB_LOCAL) $(ANAL_PLUGIN_SO) $(ARCH_PLUGIN_SO)

# Build the analysis plugin shared object
$(ANAL_PLUGIN_SO): r_anal_sleigh.c $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)
	$(CC) $(CFLAGS_SO) -o $@ $< $(LDFLAGS)
ifeq ($(UNAME),Darwin)
	@for from in "$(RUST_LINK_TARGET)" "@loader_path/$(RUST_LIB).$(RUST_LIB_EXT)"; do \
		if otool -L $@ | grep -Fq "$$from"; then \
			install_name_tool -change "$$from" "$(RUST_RUNTIME_REF)" $@; \
		fi; \
	done
	@codesign --force --sign - $@ >/dev/null
endif

# Build the architecture plugin shared object
ARCH_PLUGIN_OBJS = arch_sleigh.o r_anal_sleigh_arch.o

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

# Build Rust library (release)
rust-release:
	cd .. && cargo build --release --features $(RUST_FEATURES) -p r2sleigh-plugin
ifeq ($(UNAME),Darwin)
	install_name_tool -id @loader_path/$(RUST_LIB).$(RUST_LIB_EXT) $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)
	@codesign --force --sign - $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT) >/dev/null
endif

# Build Rust library (debug)
rust-debug:
	cd .. && cargo build --features $(RUST_FEATURES) -p r2sleigh-plugin
ifeq ($(UNAME),Darwin)
	install_name_tool -id @loader_path/$(RUST_LIB).$(RUST_LIB_EXT) $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)
	@codesign --force --sign - $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT) >/dev/null
endif

# Default rust target
ifeq ($(RUST_TARGET),release)
rust: rust-release
$(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT): rust-release
else
rust: rust-debug
$(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT): rust-debug
endif

$(RUST_LIB_LOCAL): $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT)
	mkdir -p $(RUST_RUNTIME_SUBDIR)
	rm -f $@
	cp $(RUST_BUILD_DIR)/$(RUST_LIB).$(RUST_LIB_EXT) $@
ifeq ($(UNAME),Darwin)
	@codesign --force --sign - $@ >/dev/null
endif

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
	@echo "  RUST_FEATURES - Sleigh features: 'x86' (default), 'arm' (ARM32 + AArch64), 'riscv', 'all-archs'"
	@echo ""
	@echo "Examples:"
	@echo "  make                           # Build release with x86"
	@echo "  make RUST_FEATURES=all-archs   # Build with all architectures"
	@echo "  make RUST_TARGET=debug         # Build debug version"
	@echo "  make install                   # Install to r2 plugins"
