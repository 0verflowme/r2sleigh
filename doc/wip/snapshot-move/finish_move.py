"""Second pass: strip the snapshot prototypes radare2 no longer calls, and
carry the capture's file-local types across to the plugin header."""
import re, pathlib, sys
sys.path.insert(0,'/private/tmp/claude-501')
from move import stripped_lines, F
S = pathlib.Path('/private/tmp/claude-501')

# --- 1. file-local typedefs that must travel with the capture
LOCAL_TYPES = ['RAnalTypeSnapshotBudget','FcnContextTransferKind','SnapshotTerminalFlow','SnapshotTypeGraphBuilder',
               'SnapshotTypeGraphResult','SnapshotStorageResult','SnapshotIntegerSyntax',
               'SnapshotTypeGraphSlot']
carried = []
for rel in ['libr/anal/function.c','libr/anal/type.c']:
    raw = (F/rel).read_text().splitlines(); s2 = stripped_lines('\n'.join(raw))
    for ty in LOCAL_TYPES:
        for i,l in enumerate(s2):
            if re.match(r'^\}\s*'+re.escape(ty)+r';', l):
                d=0; j=i
                while j>=0:
                    d += s2[j].count('}') - s2[j].count('{')
                    if d==0: break
                    j-=1
                carried.append('\n'.join(raw[j:i+1])); break
# the snapshot struct and its limits live in the fork's private header; the
# plugin needs the whole body, since the struct was opaque precisely because
# radare2 never wanted to look inside it
fs = (F/'libr/anal/function_snapshot.h').read_text()
body = fs
for cut in (r'/\* radare[^\n]*\n', r'#ifndef R2_ANAL_FUNCTION_SNAPSHOT_H\n', r'#define R2_ANAL_FUNCTION_SNAPSHOT_H\n',
            r'#include <r_anal\.h>\n', r'#endif[^\n]*\n?'):
    body = re.sub(cut, '', body)
body = re.sub(r'^R_IPI[^;]*;\n', '', body, flags=re.M)  # prototypes die with the move
carried.insert(0, body.strip())
print(f"carrying {len(carried)} local type blocks to the plugin header")

hdr = S/'snapshot_capture.h'
extra = S/'carried_types.txt'
carried.append(extra.read_text() if extra.exists() else '')
def _no_protos(s):
    import re as _re
    # strip prototypes from the generated header
    return _re.sub(r'^R_(API|IPI)[^;]*;\n', '', s, flags=_re.M)
hdr.write_text(
    (S/'snapshot_capture.h.in').read_text().replace('@CARRIED@',
        '/* Types the capture owns: file-local in radare2 before the move, so they\n'
        ' * travel with the code that uses them rather than staying in a header no\n'
        ' * radare2 translation unit needs any more. */\n' + _no_protos('\n\n'.join(carried))))

# --- 2. drop the snapshot prototypes radare2 no longer calls
for rel in ['libr/include/r_anal.h','libr/include/r_anal_priv.h']:
    p = F/rel; raw = p.read_text().splitlines()
    out=[]; i=0; dropped=0
    while i < len(raw):
        l = raw[i]
        if re.match(r'^R_(API|IPI)\b', l) and 'snapshot' in l.lower():
            j=i
            while j < len(raw) and not raw[j].rstrip().endswith(';'): j+=1
            # keep the two the fork itself still calls
            body=' '.join(raw[i:j+1])
            if any(k in body for k in ('r_anal_types_snapshot','r_anal_function_snapshot_free')):
                out += raw[i:j+1]
            else:
                dropped += j-i+1
            i=j+1; continue
        out.append(l); i+=1
    p.write_text('\n'.join(out)+'\n')
    print(f"  {rel}: dropped {dropped} prototype lines")


# --- 3. export the one upstream internal the capture genuinely needs
p = F/'libr/include/r_anal_priv.h'; t = p.read_text()
t = t.replace('R_IPI bool r_anal_cc_location_uses(RAnal *anal, const char *loc, const char *reg);\n', '')
p.write_text(t)
p = F/'libr/include/r_anal.h'; t = p.read_text()
if 'r_anal_cc_location_uses' not in t:
    t = t.replace('R_API R_UNOWNED RAnalPlugin *r_anal_decompiler_provider(RAnal *anal);',
"""/* True when calling convention `cc` uses register `reg` for the location
 * class `loc`. Exported because a decompiler plugin has to ask this to map a
 * convention onto the registers a function actually touches, and cannot
 * reimplement the convention database without duplicating it. */
R_API bool r_anal_cc_location_uses(RAnal *anal, const char *loc, const char *reg);
R_API R_UNOWNED RAnalPlugin *r_anal_decompiler_provider(RAnal *anal);""")
    p.write_text(t)
p = F/'libr/anal/cc.c'; t = p.read_text()
p.write_text(t.replace('R_IPI bool r_anal_cc_location_uses(', 'R_API bool r_anal_cc_location_uses('))
print("  exported r_anal_cc_location_uses")

# --- 4. drop macros in function.c that only the moved capture used
p = F/'libr/anal/function.c'; raw = p.read_text().splitlines()
DEAD = ('#define SNAPSHOT_REFUSE', '#define SNAPSHOT_MAX_CALLEE_SNAPSHOTS',
        '#undef SNAPSHOT_REFUSE')
body = '\n'.join(l for l in raw if not l.startswith('#define ') or not l.startswith(DEAD))
kept = [l for l in raw if not any(l.startswith(d) for d in DEAD)]
p.write_text('\n'.join(kept)+'\n')
print(f"  dropped {len(raw)-len(kept)} dead macro lines from function.c")


# --- 5. prototypes that clash with the plugin's now-file-local definitions.
# radare2 stopped calling these when the capture left; the declaration lingering
# in a public header is what made the plugin's static definition illegal.
clash = S/'clash.txt'
if clash.exists():
    names = clash.read_text().split()
    for rel in ['libr/include/r_anal.h','libr/include/r_anal_priv.h','libr/include/r_core.h']:
        p = F/rel; raw = p.read_text().splitlines(); out=[]; i=0; dropped=0
        while i < len(raw):
            l = raw[i]
            if re.match(r'^R_(API|IPI)\b', l) and any(re.search(r'\b'+re.escape(n)+r'\s*\(', l) for n in names):
                j=i
                while j < len(raw) and not raw[j].rstrip().endswith(';'): j+=1
                dropped += j-i+1; i=j+1; continue
            out.append(l); i+=1
        if dropped:
            p.write_text('\n'.join(out)+'\n'); print(f"  {rel}: dropped {dropped} clashing prototype lines")


# --- 6. queries that read RAnal->priv stay in radare2 and become public.
# A plugin cannot reach into radare2's private state, and these answer over
# radare2's own DWARF and exact-formal proof tables, so radare2 is the right
# place for them; what was missing was only that they were never exported.
exports = (S/'export.txt').read_text().split()
for rel in ['libr/anal/var.c','libr/anal/dwarf_process.c','libr/anal/fcn.c','libr/anal/function.c','libr/anal/type.c']:
    p = F/rel
    if not p.exists(): continue
    t = p.read_text(); before = t
    for nm in exports:
        t = re.sub(r'^R_IPI(\s+[^\n]*\b'+re.escape(nm)+r'\s*\()', r'R_API\1', t, flags=re.M)
    if t != before: p.write_text(t)
p = F/'libr/include/r_anal_priv.h'; t = p.read_text(); out=[]; moved=[]
for l in t.splitlines():
    if l.startswith('R_IPI') and any(re.search(r'\b'+re.escape(n)+r'\s*\(', l) for n in exports):
        moved.append(l.replace('R_IPI', 'R_API', 1)); continue
    out.append(l)
p.write_text('\n'.join(out)+'\n')
if moved:
    p = F/'libr/include/r_anal.h'; t = p.read_text()
    anchor = 'R_API R_UNOWNED RAnalPlugin *r_anal_decompiler_provider(RAnal *anal);'
    t = t.replace(anchor, '\n'.join(moved) + '\n' + anchor)
    p.write_text(t)
    print(f"  exported {len(moved)} private-state queries")


# --- 7. a public function's parameter types must be public too
EXPORT_TYPES = ['RAnalDwarfFramePointerStorage']
priv = F/'libr/include/r_anal_priv.h'
pub  = F/'libr/include/r_anal.h'
praw = priv.read_text().splitlines()
ps   = stripped_lines('\n'.join(praw))
ph   = pub.read_text()
kill = set()
for ty in EXPORT_TYPES:
    if re.search(r'\}\s*'+re.escape(ty)+r'\s*;', ph):
        continue
    for i, l in enumerate(ps):
        if re.match(r'^\}\s*'+re.escape(ty)+r'\s*;', l):
            d = 0; j = i
            while j >= 0:
                d += ps[j].count('}') - ps[j].count('{')
                if d == 0:
                    break
                j -= 1
            block = '\n'.join(praw[j:i+1])
            kill |= set(range(j, i+1))
            # must precede the prototypes that name it, which step 6 already
            # inserted at the same anchor
            lines = ph.splitlines()
            first = next((i for i, l in enumerate(lines)
                          if l.startswith('R_API') and ty in l), None)
            if first is None:
                first = next(i for i, l in enumerate(lines)
                             if 'r_anal_decompiler_provider' in l)
            lines.insert(first, block)
            ph = '\n'.join(lines) + '\n'
            print(f"  promoted type {ty} to the public header")
            break
if kill:
    priv.write_text('\n'.join(l for i, l in enumerate(praw) if i not in kill) + '\n')
    pub.write_text(ph)


