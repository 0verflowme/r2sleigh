"""Retire the snapshot types from radare2's public header.

Runs after the dead-code prune, because it is the prune that makes the last
references disappear: a type is only safe to remove once no radare2 file names
it, and the files that named it were themselves left dead by the move."""
import re, pathlib, sys
sys.path.insert(0, '/private/tmp/claude-501')
from move import stripped_lines, F
S = pathlib.Path('/private/tmp/claude-501')

# --- 8. STRIP_PUBLIC_TYPES: the snapshot types leave radare2's public header.
# They describe r2sleigh's view of a function, and once no radare2 translation
# unit names one, every radare2 build stops parsing 440 lines it never used.
# word-bounded: RAnalFunctionSnapshotLimits is a *private* type that stays,
# and a prefix match on it would block the strip forever
KEY = re.compile(r'\b(?:RAnalFunctionSnapshot|RAnalSnapshot[A-Za-z]*|RAnalFcnSlot|RAnalFcnContext'
                 r'|RAnalFcnCallee|R_ANAL_FUNCTION_SNAPSHOT_CAP[A-Z_]*|R_ANAL_SNAPSHOT[A-Z_]*'
                 r'|RAnalFunctionImageSnapshot|RAnalFunctionInterfaceSnapshot'
                 r'|RAnalCallSiteInterfaceSnapshot|RAnalFunctionSnapshotView'
                 r'|RAnalFunctionSnapshotCallback)\b')
still = []
for c in list(F.glob('libr/**/*.c')) + list(F.glob('libr/**/*.inc.c')):
    if 'function_snapshot' in str(c): continue
    if KEY.search(c.read_text(errors='replace')): still.append(str(c.relative_to(F)))
if still:
    print(f"  keeping snapshot types in r_anal.h; still used by {still}")
else:
    p = F/'libr/include/r_anal.h'
    raw = p.read_text().splitlines(); s2 = stripped_lines('\n'.join(raw))
    kill = set(); i = 0
    while i < len(s2):
        l = s2[i]
        if l.startswith(('typedef','struct ','enum ','#define')):
            d=0; seen=False; j=i
            while j < len(s2):
                d += s2[j].count('{') - s2[j].count('}')
                if '{' in s2[j]: seen = True
                if seen and d <= 0: break
                if not seen and s2[j].rstrip().endswith(';'): break
                if not seen and s2[j].rstrip().endswith('\\'): j += 1; continue
                if not seen and j > i+3: break
                j += 1
            if j < len(s2) and KEY.search('\n'.join(raw[i:j+1])):
                kill |= set(range(i, j+1))
            i = j+1; continue
        i += 1
    if kill:
        p.write_text('\n'.join(l for k,l in enumerate(raw) if k not in kill) + '\n')
        print(f"  r_anal.h: dropped {len(kill)} snapshot type lines")
        # hand them to the plugin, ahead of the header content that names them
        moved_types = '\n'.join(l for k,l in enumerate(raw) if k in kill)
        hdr = S/'snapshot_capture.h'
        h = hdr.read_text()
        if 'snapshot types, retired from r_anal.h' not in h:
            h = h.replace('#include <r_core.h>\n',
                '#include <r_core.h>\n\n/* The snapshot types, retired from r_anal.h. They describe r2sleigh\'s\n'
                ' * view of a function, so every radare2 translation unit was parsing a\n'
                ' * description of something it never touched. */\n' + moved_types + '\n')
            hdr.write_text(h)
        # the free() prototype names a type radare2 no longer has, and radare2
        # no longer calls it either
        pv = F/'libr/include/r_anal_priv.h'
        pt = pv.read_text()
        pt = re.sub(r'^R_IPI[^;\n]*r_anal_function_snapshot_free[^;]*;\n', '', pt, flags=re.M)
        pv.write_text(pt)
        # function_snapshot.h described the snapshot itself; radare2 keeps only
        # the limits struct, which its own type budget still enforces.
        fsp = F/'libr/anal/function_snapshot.h'
        fs = fsp.read_text()
        m = re.search(r'#define R_ANAL_FUNCTION_SNAPSHOT_LIMITS_VERSION.*?\} RAnalFunctionSnapshotLimits;', fs, re.S)
        if m:
            fsp.write_text(
                '/* Capture limits radare2 still enforces on its own type budget.\n'
                ' *\n'
                ' * The snapshot this file used to describe now lives in the r2sleigh\n'
                ' * plugin; what stays is the bound radare2 checks for itself. */\n\n'
                '#ifndef R2_ANAL_FUNCTION_SNAPSHOT_H\n'
                '#define R2_ANAL_FUNCTION_SNAPSHOT_H\n\n'
                '#include <r_anal.h>\n\n' + m.group(0) + '\n\n#endif\n')
            print("  function_snapshot.h reduced to the limits radare2 enforces")
