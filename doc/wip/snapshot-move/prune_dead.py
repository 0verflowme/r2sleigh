"""Remove declarations left dangling by the move.

Precise by construction: the only things removed are declarations naming a
function that this move relocated, read from movable.txt. An earlier version
inferred deadness from a span parser and deleted live upstream code three
separate ways -- ReadAhead in fcn.c, get_functions_block_cb in function.c --
so nothing here guesses."""
import re, pathlib, sys
sys.path.insert(0, '/private/tmp/claude-501')
from move import stripped_lines, F

S = pathlib.Path('/private/tmp/claude-501')
moved = {l.split('\t')[0] for l in (S/'movable.txt').read_text().splitlines() if l.strip()}

for rel in ['libr/anal/function.c', 'libr/anal/type.c']:
    p = F/rel
    if not p.exists():
        continue
    raw = p.read_text().splitlines()
    s2 = stripped_lines('\n'.join(raw))
    dead = set()
    i = 0
    while i < len(s2):
        m = re.match(r'^(?:static|R_API|R_IPI)\s+.*?\b([a-z_0-9]+)\s*\(', s2[i])
        if m and m.group(1) in moved:
            j = i
            ok = True
            while j < len(s2):
                if '{' in s2[j]:            # a definition, not a declaration
                    ok = False
                    break
                if s2[j].rstrip().endswith(';'):
                    break
                j += 1
            if ok and j < len(s2):
                dead |= set(range(i, j + 1))
                i = j + 1
                continue
        i += 1
    if dead:
        p.write_text('\n'.join(l for k, l in enumerate(raw) if k not in dead) + '\n')
        print(f"  {rel}: removed {len(dead)} declarations of moved functions")

# Definitions the move duplicated into the plugin and left dead here.
# The criterion is exact rather than inferred: the identifier must occur exactly
# once in the whole of libr, which can only be its own definition. The counts
# come from one pass over the tree -- grepping per name took over ten minutes.
from move import function_spans
import collections

def tree_counts():
    c = collections.Counter()
    for f in list(F.glob('libr/**/*.c')) + list(F.glob('libr/**/*.h')) + list(F.glob('libr/**/*.inc.c')):
        c.update(re.findall(r'\b[A-Za-z_][A-Za-z_0-9]*\b', f.read_text(errors='replace')))
    return c

for rel in ['libr/anal/function.c']:
    p = F/rel
    if not p.exists():
        continue
    for _pass in range(4):
        counts = tree_counts()
        raw, spans = function_spans(p)
        s2 = stripped_lines('\n'.join(raw))
        dead = set()
        for nm, (a, b) in spans.items():
            if counts[nm] == 1:
                dead |= set(range(a, b + 1))
        i = 0
        while i < len(s2):
            if s2[i].startswith(('typedef struct', 'typedef enum')):
                d = 0; seen = False; j = i
                while j < len(s2):
                    d += s2[j].count('{') - s2[j].count('}')
                    if '{' in s2[j]: seen = True
                    if seen and d <= 0: break
                    j += 1
                if j < len(s2):
                    m = re.match(r'^\}\s*([A-Za-z_0-9]+)\s*;', s2[j])
                    if m and counts[m.group(1)] == 1:
                        dead |= set(range(i, j + 1))
                    i = j + 1; continue
            i += 1
        if not dead:
            break
        p.write_text('\n'.join(l for k, l in enumerate(raw) if k not in dead) + '\n')
        print(f"  {rel}: removed {len(dead)} lines whose only mention was their own definition")
