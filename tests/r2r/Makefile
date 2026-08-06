# r2r test harness for r2sleigh plugin

# Keep the default harness deterministic. Parallel r2r runs intermittently
# miss symbolic-path coverage on stress_parse_number under this workspace/toolchain.
R2R_JOBS ?= 1
R2R_TIMEOUT ?= 120
R2R_ARGS ?= db/extras
R2R_TMPDIR ?= /tmp/r2sleigh-r2r-tmp
R2R_PLUGIN_DIR ?= $(R2R_TMPDIR)/plugins
R2R_RUST_FEATURES ?= all-archs
R2R_PLUGIN_RUNTIME_SUBDIR ?= r2sleigh
SOURCE_GOLD_TIMEOUT ?= 120
SOURCE_GOLD_JOBS ?= 1
SOURCE_GOLD_COMMANDS ?= decompile_sla,types,profile
SOURCE_GOLD_TMPDIR ?= /tmp/r2sleigh-source-gold-tmp
SOURCE_GOLD_PLUGIN_DIR ?= $(SOURCE_GOLD_TMPDIR)/plugins
SOURCE_GOLD_OUT ?= /tmp/r2sleigh-source-gold-current.json
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
SHARED_EXT := dylib
else
SHARED_EXT := so
endif
LOCAL_PLUGIN_DIR := $(abspath ../../r2plugin)
LOCAL_R2_DIR ?= ../../../radare2
LOCAL_R2_ABS := $(abspath $(LOCAL_R2_DIR))
LOCAL_R2_BIN := $(LOCAL_R2_ABS)/binr/radare2/radare2
LOCAL_R2_ANAL_SO := $(LOCAL_R2_ABS)/libr/anal/libr_anal.$(SHARED_EXT)
LOCAL_R2_LD_LIBRARY_PATH := $(shell find "$(LOCAL_R2_ABS)/libr" -mindepth 1 -maxdepth 1 -type d 2>/dev/null | sort | paste -sd: -)
E2E_DIR := ../e2e
MANUAL_SRC := ../gold/manual_limits.c
MANUAL_BINS := \
	bins/r2sleigh_manual_limits_O0 \
	bins/r2sleigh_manual_limits_O2
E2E_BINS := \
	$(E2E_DIR)/vuln_test \
	$(E2E_DIR)/stress_test \
	$(E2E_DIR)/stress_test_opt \
	$(E2E_DIR)/vuln_test_x86 \
	$(E2E_DIR)/stress_test_x86 \
	$(E2E_DIR)/stress_test_opt_x86

ifneq ($(wildcard $(E2E_DIR)/test_func.c),)
E2E_BINS += $(E2E_DIR)/test_func $(E2E_DIR)/test_func_x86
endif

ifneq ($(wildcard $(E2E_DIR)/sym_test.c),)
E2E_BINS += $(E2E_DIR)/sym_test $(E2E_DIR)/sym_test_x86
endif

ifeq ($(wildcard $(LOCAL_R2_BIN)),$(LOCAL_R2_BIN))
ifeq ($(wildcard $(LOCAL_R2_ANAL_SO)),$(LOCAL_R2_ANAL_SO))
R2R_RADARE2 ?= $(LOCAL_R2_BIN)
R2R_LD_LIBRARY_PATH ?= $(LOCAL_R2_LD_LIBRARY_PATH)
endif
endif

R2R_RADARE2 ?= radare2
R2R_LD_LIBRARY_PATH ?=

.PHONY: all ensure-tools build-bins link-bins install-plugin run source-gold

all: run

ensure-tools:
	@[ -x "$(R2R_RADARE2)" ] || command -v "$(R2R_RADARE2)" >/dev/null || { echo "radare2 not found: $(R2R_RADARE2)"; exit 1; }
	@command -v r2r >/dev/null || { echo "r2r not found in PATH"; exit 1; }
	@command -v jq >/dev/null || { echo "jq not found in PATH"; exit 1; }
	@command -v python3 >/dev/null || { echo "python3 not found in PATH"; exit 1; }

build-bins: $(E2E_BINS) $(MANUAL_BINS)

$(E2E_DIR)/vuln_test: $(E2E_DIR)/vuln_test.c
	gcc -O0 -g -fno-stack-protector -no-pie -o $@ $<

$(E2E_DIR)/stress_test: $(E2E_DIR)/stress_test.c
	gcc -O0 -g -fno-stack-protector -no-pie -o $@ $< -lm

$(E2E_DIR)/stress_test_opt: $(E2E_DIR)/stress_test.c
	gcc -O2 -g -fno-stack-protector -no-pie -o $@ $< -lm

$(E2E_DIR)/test_func: $(E2E_DIR)/test_func.c
	gcc -O0 -g -o $@ $<

$(E2E_DIR)/sym_test: $(E2E_DIR)/sym_test.c
	gcc -O0 -g -o $@ $<

bins/r2sleigh_manual_limits_O0: $(MANUAL_SRC)
	@mkdir -p bins
	gcc -O0 -g -fno-inline -fno-omit-frame-pointer -fno-stack-protector -no-pie -o $@ $<

bins/r2sleigh_manual_limits_O2: $(MANUAL_SRC)
	@mkdir -p bins
	gcc -O2 -g -fno-inline -fno-omit-frame-pointer -fno-stack-protector -no-pie -o $@ $<

ifeq ($(UNAME_S),Darwin)
$(E2E_DIR)/vuln_test_x86: $(E2E_DIR)/vuln_test.c
	clang -arch x86_64 -Wl,-no_pie -O0 -g -fno-stack-protector -o $@ $<

$(E2E_DIR)/stress_test_x86: $(E2E_DIR)/stress_test.c
	clang -arch x86_64 -Wl,-no_pie -O0 -g -fno-stack-protector -o $@ $< -lm

$(E2E_DIR)/stress_test_opt_x86: $(E2E_DIR)/stress_test.c
	clang -arch x86_64 -Wl,-no_pie -O2 -g -fno-stack-protector -o $@ $< -lm

$(E2E_DIR)/test_func_x86: $(E2E_DIR)/test_func.c
	clang -arch x86_64 -Wl,-no_pie -O0 -g -o $@ $<

$(E2E_DIR)/sym_test_x86: $(E2E_DIR)/sym_test.c
	clang -arch x86_64 -Wl,-no_pie -O0 -g -o $@ $<
else
$(E2E_DIR)/vuln_test_x86: $(E2E_DIR)/vuln_test.c
	gcc -m64 -O0 -g -fno-stack-protector -no-pie -o $@ $<

$(E2E_DIR)/stress_test_x86: $(E2E_DIR)/stress_test.c
	gcc -m64 -O0 -g -fno-stack-protector -no-pie -o $@ $< -lm

$(E2E_DIR)/stress_test_opt_x86: $(E2E_DIR)/stress_test.c
	gcc -m64 -O2 -g -fno-stack-protector -no-pie -o $@ $< -lm

$(E2E_DIR)/test_func_x86: $(E2E_DIR)/test_func.c
	gcc -m64 -O0 -g -o $@ $<

$(E2E_DIR)/sym_test_x86: $(E2E_DIR)/sym_test.c
	gcc -m64 -O0 -g -o $@ $<
endif

link-bins: build-bins
	@mkdir -p bins
	@ln -sf ../../e2e/vuln_test bins/vuln_test
	@ln -sf ../../e2e/stress_test bins/stress_test
	@ln -sf ../../e2e/stress_test_opt bins/stress_test_opt
	@ln -sf ../../e2e/vuln_test_x86 bins/vuln_test_x86
	@ln -sf ../../e2e/stress_test_x86 bins/stress_test_x86
	@ln -sf ../../e2e/stress_test_opt_x86 bins/stress_test_opt_x86
	@if [ -f ../e2e/test_func ]; then ln -sf ../../e2e/test_func bins/test_func; fi
	@if [ -f ../e2e/sym_test ]; then ln -sf ../../e2e/sym_test bins/sym_test; fi
	@if [ -f ../e2e/test_func_x86 ]; then ln -sf ../../e2e/test_func_x86 bins/test_func_x86; fi
	@if [ -f ../e2e/sym_test_x86 ]; then ln -sf ../../e2e/sym_test_x86 bins/sym_test_x86; fi

install-plugin:
	@mkdir -p "$(R2R_PLUGIN_DIR)"
	@mkdir -p "$(R2R_PLUGIN_DIR)/$(R2R_PLUGIN_RUNTIME_SUBDIR)"
	$(MAKE) -C ../../r2plugin RUST_FEATURES=$(R2R_RUST_FEATURES) LOCAL_R2_DIR="$(LOCAL_R2_ABS)" R2_PLUGIN_DIR="$(abspath $(R2R_PLUGIN_DIR))" install

run: ensure-tools link-bins
	@rm -rf "$(R2R_TMPDIR)"
	@mkdir -p "$(R2R_TMPDIR)" "$(R2R_PLUGIN_DIR)" "$(R2R_TMPDIR)/xdg-data"
	@$(MAKE) install-plugin R2R_PLUGIN_DIR="$(R2R_PLUGIN_DIR)"
	TMPDIR="$(R2R_TMPDIR)" TMP="$(R2R_TMPDIR)" TEMP="$(R2R_TMPDIR)" \
		R2R_RADARE2="$(R2R_RADARE2)" \
		XDG_DATA_HOME="$(abspath $(R2R_TMPDIR)/xdg-data)" \
		R2_LIBR_PLUGINS="$(abspath $(R2R_PLUGIN_DIR))" \
		LD_LIBRARY_PATH="$(R2R_LD_LIBRARY_PATH)$${LD_LIBRARY_PATH:+:$$LD_LIBRARY_PATH}" \
		DYLD_LIBRARY_PATH="$(R2R_LD_LIBRARY_PATH)$${DYLD_LIBRARY_PATH:+:$$DYLD_LIBRARY_PATH}" \
		r2r -t $(R2R_TIMEOUT) -j $(R2R_JOBS) -L $(R2R_ARGS)

source-gold: ensure-tools link-bins
	@rm -rf "$(SOURCE_GOLD_TMPDIR)"
	@mkdir -p "$(SOURCE_GOLD_TMPDIR)" "$(SOURCE_GOLD_PLUGIN_DIR)" "$(SOURCE_GOLD_TMPDIR)/xdg-data"
	@$(MAKE) install-plugin R2R_PLUGIN_DIR="$(SOURCE_GOLD_PLUGIN_DIR)"
	cd ../.. && \
		TMPDIR="$(SOURCE_GOLD_TMPDIR)" TMP="$(SOURCE_GOLD_TMPDIR)" TEMP="$(SOURCE_GOLD_TMPDIR)" \
		XDG_DATA_HOME="$(abspath $(SOURCE_GOLD_TMPDIR)/xdg-data)" \
		R2_LIBR_PLUGINS="$(abspath $(SOURCE_GOLD_PLUGIN_DIR))" \
		LD_LIBRARY_PATH="$(R2R_LD_LIBRARY_PATH)$${LD_LIBRARY_PATH:+:$$LD_LIBRARY_PATH}" \
		DYLD_LIBRARY_PATH="$(R2R_LD_LIBRARY_PATH)$${DYLD_LIBRARY_PATH:+:$$DYLD_LIBRARY_PATH}" \
		python3 scripts/reversing_benchmark.py \
			--manifest tests/gold/closure_manifest.json \
			--gold-manifest tests/gold/source_oracle.json \
			--manifest-only \
			--closure-gate \
			--commands "$(SOURCE_GOLD_COMMANDS)" \
			--analysis aaa \
			--timeout "$(SOURCE_GOLD_TIMEOUT)" \
			--jobs "$(SOURCE_GOLD_JOBS)" \
			--plugin-dir "$(abspath $(SOURCE_GOLD_PLUGIN_DIR))" \
			--r2 "$(R2R_RADARE2)" \
			--tmpdir "$(abspath $(SOURCE_GOLD_TMPDIR))/bench" \
			--out "$(SOURCE_GOLD_OUT)"
