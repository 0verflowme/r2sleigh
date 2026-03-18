# r2r test harness for r2sleigh plugin

# Keep the default harness deterministic. Parallel r2r runs intermittently
# miss symbolic-path coverage on stress_parse_number under this workspace/toolchain.
R2R_JOBS ?= 1
R2R_TIMEOUT ?= 120
R2R_TMPDIR ?= /tmp/r2sleigh-r2r-tmp
R2R_PLUGIN_DIR ?= $(R2R_TMPDIR)/plugins
R2R_RUST_FEATURES ?= all-archs
UNAME_S := $(shell uname -s)

.PHONY: all ensure-tools build-bins link-bins install-plugin run

all: run

ensure-tools:
	@command -v r2 >/dev/null || { echo "r2 not found in PATH"; exit 1; }
	@command -v r2r >/dev/null || { echo "r2r not found in PATH"; exit 1; }
	@command -v jq >/dev/null || { echo "jq not found in PATH"; exit 1; }
	@command -v python3 >/dev/null || { echo "python3 not found in PATH"; exit 1; }

build-bins:
	cd ../e2e && \
	gcc -O0 -g -fno-stack-protector -no-pie -o vuln_test vuln_test.c && \
	gcc -O0 -g -fno-stack-protector -no-pie -o stress_test stress_test.c -lm && \
	gcc -O2 -g -fno-stack-protector -no-pie -o stress_test_opt stress_test.c -lm && \
	if [ -f test_func.c ]; then gcc -O0 -g -o test_func test_func.c; fi && \
	if [ -f sym_test.c ]; then gcc -O0 -g -o sym_test sym_test.c; fi
	cd ../e2e && \
	if [ "$(UNAME_S)" = "Darwin" ]; then \
		clang -arch x86_64 -Wl,-no_pie -O0 -g -fno-stack-protector -o vuln_test_x86 vuln_test.c; \
		clang -arch x86_64 -Wl,-no_pie -O0 -g -fno-stack-protector -o stress_test_x86 stress_test.c -lm; \
		clang -arch x86_64 -Wl,-no_pie -O2 -g -fno-stack-protector -o stress_test_opt_x86 stress_test.c -lm; \
		if [ -f test_func.c ]; then clang -arch x86_64 -Wl,-no_pie -O0 -g -o test_func_x86 test_func.c; fi; \
		if [ -f sym_test.c ]; then clang -arch x86_64 -Wl,-no_pie -O0 -g -o sym_test_x86 sym_test.c; fi; \
	else \
		gcc -m64 -O0 -g -fno-stack-protector -no-pie -o vuln_test_x86 vuln_test.c; \
		gcc -m64 -O0 -g -fno-stack-protector -no-pie -o stress_test_x86 stress_test.c -lm; \
		gcc -m64 -O2 -g -fno-stack-protector -no-pie -o stress_test_opt_x86 stress_test.c -lm; \
		if [ -f test_func.c ]; then gcc -m64 -O0 -g -o test_func_x86 test_func.c; fi; \
		if [ -f sym_test.c ]; then gcc -m64 -O0 -g -o sym_test_x86 sym_test.c; fi; \
	fi

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
	$(MAKE) -C ../../r2plugin RUST_FEATURES=$(R2R_RUST_FEATURES) R2_PLUGIN_DIR="$(abspath $(R2R_PLUGIN_DIR))" install

run: ensure-tools link-bins
	@rm -rf "$(R2R_TMPDIR)"
	@mkdir -p "$(R2R_TMPDIR)" "$(R2R_PLUGIN_DIR)" "$(R2R_TMPDIR)/xdg-data"
	@$(MAKE) install-plugin R2R_PLUGIN_DIR="$(R2R_PLUGIN_DIR)"
	TMPDIR="$(R2R_TMPDIR)" TMP="$(R2R_TMPDIR)" TEMP="$(R2R_TMPDIR)" \
		XDG_DATA_HOME="$(abspath $(R2R_TMPDIR)/xdg-data)" \
		R2_LIBR_PLUGINS="$(abspath $(R2R_PLUGIN_DIR))" \
		r2r -t $(R2R_TIMEOUT) -j $(R2R_JOBS) -L db/extras
