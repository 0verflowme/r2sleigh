"""Carry named type definitions from the fork into the plugin header.

Blocks are emitted in their original file order: a struct carried in one round
and the enum it contains carried in the next must still come out in an order C
accepts, so accumulation order cannot be the emission order."""
import re, pathlib, sys, json
sys.path.insert(0,'/private/tmp/claude-501')
from move import stripped_lines, F
S = pathlib.Path('/private/tmp/claude-501')
want = set(sys.argv[1:])
store = S/'carried_types.json'
have = json.loads(store.read_text()) if store.exists() else {}
want -= set(have)
found = {}
for p in sorted(list(F.glob('libr/**/*.h')) + list(F.glob('libr/**/*.c'))):
    if not want: break
    rel = str(p.relative_to(F))
    raw = p.read_text(errors='replace').splitlines(); s2 = stripped_lines('\n'.join(raw))
    for ty in list(want):
        for i,l in enumerate(s2):
            if re.match(r'^\}\s*'+re.escape(ty)+r'\s*;', l):
                d=0; j=i
                while j>=0:
                    d += s2[j].count('}') - s2[j].count('{')
                    if d==0: break
                    j-=1
                found[ty]=[rel, j, '\n'.join(raw[j:i+1])]; want.discard(ty); break
            if re.match(r'^typedef\s+[^{}]*\b'+re.escape(ty)+r'\s*;', l):
                found[ty]=[rel, i, raw[i]]; want.discard(ty); break
            # object-like and function-like macros, continuation lines included
            if re.match(r'^#define\s+'+re.escape(ty)+r'\b', raw[i]):
                j=i
                while j < len(raw) and raw[j].rstrip().endswith('\\'): j+=1
                found[ty]=[rel, i, '\n'.join(raw[i:j+1])]; want.discard(ty); break
have.update(found)
store.write_text(json.dumps(have))
ordered = sorted(have.values(), key=lambda v: (v[0], v[1]))
(S/'carried_types.txt').write_text('\n\n'.join(v[2] for v in ordered) + '\n')
print(f"carried {len(found)} new ({len(have)} total); unresolved: {sorted(want)}")
