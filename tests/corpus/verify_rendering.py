#!/usr/bin/env python3
"""Compile each rendered function and run it against the reference hash.

Structural soundness is not correctness. The only claim that settles it is that
the C on the page, compiled and run on the same input, produces the same value
the original binary produced. Renderings that will not compile are reported as
such rather than counted either way.
"""
import re, subprocess, sys, os, json

CFG = sys.argv[1] if len(sys.argv) > 1 else 'arm64_O2'
MSG = "The quick brown fox jumps over the lazy dog, 0123456789abcdef"
REF = {}
for line in open('reference.txt'):
    parts = line.split()
    if len(parts) == 2:
        REF[parts[0]] = parts[1]

# name -> (result C type, printf spec, call arity source, extra args)
SPEC = {
    'fnv1a32':   ('unsigned int',       '%08x',  2, []),
    'fnv1a64':   ('unsigned long long', '%016llx', 2, []),
    'djb2':      ('unsigned int',       '%08x',  2, []),
    'sdbm':      ('unsigned int',       '%08x',  2, []),
    'adler32':   ('unsigned int',       '%08x',  2, []),
    'crc32_bitwise': ('unsigned int',   '%08x',  2, []),
    'pearson':   ('unsigned char',      '%02x',  2, []),
    'murmur3_32':('unsigned int',       '%08x',  3, ['0x9747b28cu']),
    'xxhash32':  ('unsigned int',       '%08x',  3, ['0']),
}
REFKEY = {'crc32_bitwise': 'crc32_bit'}

def blocks(path):
    text = open(path).read()
    for chunk in re.split(r'════+ ', text)[1:]:
        name = chunk.split('\n', 1)[0].strip()
        body = chunk[len(name):]
        m = re.search(r'^(\S.*?sym\._\w+\(.*?\))\s*$', body, re.M)
        if not m:
            continue
        start = body.index(m.group(1))
        yield name, body[start:]

def repair(src, name):
    """One rendering, made compilable without changing what it computes.

    Every parameter and local becomes `long`, and each dereference is given an
    explicit cast, because a rendering types an address-carrying value as an
    integer and then dereferences it. Where the rendering states a width the cast
    uses it; where it states none the harness has to assume one, and that is
    counted, because C that does not say how wide a load is has not said what the
    program does.
    """
    assumed = 0
    src = re.sub(r'\bsym\._' + re.escape(name) + r'\b', 'dec_' + name, src)
    sig_end = src.index(')')
    sig, rest = src[:sig_end + 1], src[sig_end + 1:]
    params = sig[sig.index('(') + 1:-1].strip()
    n = 0
    if params and params != 'void':
        n = len(params.split(','))
        sig = sig[:sig.index('(') + 1] + ', '.join(
            f'long arg{i}' for i in range(n)) + ')'
    sig = re.sub(r'^\S+\s+dec_', 'long dec_', sig)
    rest = re.sub(r'/\*.*?\*/', '', rest, flags=re.S)
    rest = re.sub(r'\b(?:u?int(?:8|16|32|64|128|512)_t)\s+(\w+)', r'long \1', rest)
    # a stated width keeps its width
    rest = re.sub(r'\*\s*\(\s*(u?int(?:8|16|32|64)_t)\s*\*\s*\)\s*',
                  r'@@D\1@@', rest)
    # `name[index]` on an integer-typed value
    def idx(m):
        nonlocal assumed
        assumed += 1
        return f'(((unsigned char *)(long)({m.group(1)}))[{m.group(2)}])'
    prev = None
    while prev != rest:
        prev = rest
        rest = re.sub(r'([A-Za-z_]\w*|0[xX][0-9a-fA-F]+[uU]?)\s*\[([^\[\]]+)\]', idx, rest)
        rest = re.sub(r'\(([^()\[\]]*)\)\s*\[([^\[\]]+)\]', idx, rest)
    # a bare dereference states no width at all. `*x` is a load and `a * b` is a
    # product; this codegen always spaces the operator and never the load.
    def bare(m):
        nonlocal assumed
        assumed += 1
        return f'(*(unsigned char *)(long)({m.group(1)}))'
    rest = re.sub(r'\*\(([^()]*)\)', bare, rest)
    rest = re.sub(r'\*([A-Za-z_]\w*)\b', bare, rest)
    rest = re.sub(r'@@D(u?int(?:8|16|32|64)_t)@@', r'*(\1 *)(long)', rest)
    return sig + rest, n, assumed

results = {}
os.makedirs('verify', exist_ok=True)
for name, src in blocks(f'out_{CFG}.txt'):
    if name not in SPEC:
        continue
    rtype, spec, arity, extra = SPEC[name]
    fixed, n, assumed = repair(src, name)
    if n == 0:
        results[name] = ('nosig', '')
        continue
    args = ['(long)msg', 'n'] + [f'(long)({e})' for e in extra]
    args += ['0'] * max(0, n - len(args))
    call = ', '.join(args[:n])
    prog = f'''#include <stdio.h>
#include <stdint.h>
#include <string.h>
static const char msg[] = "{MSG}";
{fixed}
int main(void) {{
    long n = sizeof(msg) - 1;
    printf("{spec}\\n", ({rtype})dec_{name}({call}));
    return 0;
}}
'''
    path = f'verify/{CFG}_{name}.c'
    open(path, 'w').write(prog)
    cc = subprocess.run(
        ['clang', '-w', '-Wno-error=int-conversion',
         '-Wno-error=incompatible-pointer-types', '-Wno-error=int-to-pointer-cast',
         '-O0', '-o', f'verify/{CFG}_{name}', path],
        capture_output=True, text=True)
    if cc.returncode != 0:
        first = next((l for l in cc.stderr.splitlines() if 'error:' in l), '')
        results[name] = ('nocompile', first.strip()[:90])
        continue
    try:
        run = subprocess.run([f'./verify/{CFG}_{name}'], capture_output=True,
                             text=True, timeout=5)
    except subprocess.TimeoutExpired:
        results[name] = ('hang', 'did not terminate')
        continue
    got = run.stdout.strip()
    want = REF.get(REFKEY.get(name, name), '?')
    note = f'{got} want {want}'
    if assumed:
        note += f' [{assumed} width(s) assumed]'
    results[name] = ('CORRECT' if got == want else 'wrong', note)

print(f'== {CFG}')
for name in SPEC:
    if name in results:
        verdict, detail = results[name]
        print(f'  {name:<15}{verdict:<11}{detail}')
tally = {}
for verdict, _ in results.values():
    tally[verdict] = tally.get(verdict, 0) + 1
print(' ', tally)
