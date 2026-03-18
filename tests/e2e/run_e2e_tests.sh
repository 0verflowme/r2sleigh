#!/bin/bash
# End-to-end tests for r2sleigh using radare2

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
R2SLEIGH_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
TEST_BINARY="$SCRIPT_DIR/test_func"
case "$(uname)" in
  Darwin) PLUGIN_LIB="$R2SLEIGH_ROOT/target/release/libr2sleigh_plugin.dylib" ;;
  *) PLUGIN_LIB="$R2SLEIGH_ROOT/target/release/libr2sleigh_plugin.so" ;;
esac

echo "=== r2sleigh End-to-End Tests ==="
echo "Test binary: $TEST_BINARY"
echo "Plugin: $PLUGIN_LIB"
echo ""

# Check prerequisites
if [ ! -f "$TEST_BINARY" ]; then
    echo "Building test binary..."
    gcc -O0 -g -o "$TEST_BINARY" "$SCRIPT_DIR/test_func.c"
fi

if [ ! -f "$PLUGIN_LIB" ]; then
    echo "ERROR: Plugin not found. Run: cargo build --release -p r2sleigh-plugin"
    exit 1
fi

# Test 1: Basic radare2 analysis
echo "--- Test 1: Basic radare2 analysis ---"
r2 -q -c "aaa; afl" "$TEST_BINARY" | head -20
echo ""

# Test 2: Disassemble add function
echo "--- Test 2: Disassemble 'add' function ---"
r2 -q -c "aaa; s sym.add; pdf" "$TEST_BINARY" 2>/dev/null || echo "(function not found with sym.add, trying different name)"
echo ""

# Test 3: Get ESIL for instructions
echo "--- Test 3: ESIL output ---"
r2 -q -c "aaa; s sym.add; e asm.esil=true; pd 5" "$TEST_BINARY" 2>/dev/null | head -10
echo ""

# Test 4: Basic blocks for factorial (has branches)
echo "--- Test 4: Basic blocks for 'factorial' ---"
r2 -q -c "aaa; s sym.factorial; afb" "$TEST_BINARY" 2>/dev/null | head -10
echo ""

# Test 5: CFG for sum_array (has loop)
echo "--- Test 5: CFG for 'sum_array' ---"
r2 -q -c "aaa; s sym.sum_array; agf" "$TEST_BINARY" 2>/dev/null | head -30
echo ""

# Test 6: Variables analysis
echo "--- Test 6: Variables in 'sum_array' ---"
r2 -q -c "aaa; s sym.sum_array; afv" "$TEST_BINARY" 2>/dev/null | head -10
echo ""

# Test 7: Cross-references
echo "--- Test 7: Cross-references to 'add' ---"
r2 -q -c "aaa; s sym.add; axt" "$TEST_BINARY" 2>/dev/null | head -5
echo ""

# Test 8: Native decompilation (if pdg is available)
echo "--- Test 8: Native decompilation (pdg) ---"
r2 -q -c "aaa; s sym.add; pdg" "$TEST_BINARY" 2>/dev/null || echo "(pdg not available - r2ghidra not installed)"
echo ""

echo "=== All basic tests completed ==="
