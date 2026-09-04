"""Copy helpers both sides need into the plugin as file-local functions.

Exporting them instead would grow radare2's public API to serve one plugin,
which is the thing this whole move exists to undo. They are small, and a
duplicated ten-line hash mixer is a smaller cost than a permanent export."""
import re, pathlib, sys
sys.path.insert(0,'/private/tmp/claude-501')
from move import function_spans, F
S = pathlib.Path('/private/tmp/claude-501')
cap = S/'snapshot_capture.c'
text = cap.read_text()
defined = set(re.findall(r'^static [^;\n]*?\b([a-z_0-9]+)\s*\(', text, re.M))
called  = set(re.findall(r'\b([a-z_][a-z_0-9]*)\s*\(', text))
missing = called - defined
# anything radare2 exports is called, never copied
public = set()
for h in (F/'libr/include').rglob('*.h'):
    for l in h.read_text(errors='replace').splitlines():
        s=l.lstrip()
        # R_IPI is hidden by -fvisibility=hidden, so a plugin cannot link it:
        # those get duplicated like any other file-local helper. Only R_API
        # (possibly behind R_DEPRECATE/R_OWNED/R_UNOWNED) is callable.
        if s.startswith('R_API') or s.startswith(('R_DEPRECATE','R_BORROW','R_OWNED','R_UNOWNED')) and 'R_API' in s \
           or s.startswith('extern') or 'static inline' in s:
            import re as _re
            public |= set(_re.findall(r'\b([a-z_][a-z_0-9]*)\s*\(', l))
missing -= public
exported = set((S/'export.txt').read_text().split()) if (S/'export.txt').exists() else set()
public |= exported   # these stay in radare2: they read RAnal->priv, which a plugin must not
missing -= exported
FILES = ['libr/anal/function.c','libr/anal/type.c','libr/anal/cc.c','libr/anal/fcn.c',
         'libr/anal/var.c','libr/anal/xrefs.c','libr/anal/anal.c','libr/util/utype.c',
         'libr/core/canal.c','libr/core/canal_artifacts.c']
added=[]
def sweep(text):
    """One pass: return bodies for file-local callees `text` lacks."""
    have = set(re.findall(r'^static [^;\n]*?\b([a-z_0-9]+)\s*\(', text, re.M)) | {n for n,_ in added}
    called_syntax = set(re.findall(r'\b([a-z_][a-z_0-9]*)\s*\(', text))
    # a callback passed by name has no '(' after it, so it cannot be found by
    # syntax; those names come from the compiler via dupforce.txt rather than
    # by treating every bare word as a call, which over-matched badly
    forced = set((S/'dupforce.txt').read_text().split()) if (S/'dupforce.txt').exists() else set()
    need = (called_syntax | (forced & set(re.findall(r'\b([a-z_][a-z_0-9]*)\b', text)))) - have - public
    out=[]
    for rel in FILES:
        p = F/rel
        if not p.exists(): continue
        raw, spans = function_spans(p)
        for nm in sorted(need & set(spans)):
            if nm in {x for x,_ in added} or nm in {x for x,_ in out}: continue
            a,b = spans[nm]
            body = list(raw[a:b+1])
            body[0] = re.sub(r'^(R_API|R_IPI)\s+', 'static ', body[0])
            if not body[0].lstrip().startswith('static'): body[0] = 'static ' + body[0]
            out.append((nm, '\n'.join(body)))
    return out
for _round in range(8):
    got = sweep(text + '\n'.join(b for _,b in added))
    if not got: break
    added += got
for rel in []:
    p = F/rel
    if not p.exists(): continue
    raw, spans = function_spans(p)
    for nm in sorted(missing & set(spans)):
        if nm in {x for x,_ in added}: continue
        a,b = spans[nm]
        body = list(raw[a:b+1])
        body[0] = re.sub(r'^(R_API|R_IPI)\s+', 'static ', body[0])
        if not body[0].lstrip().startswith('static'): body[0] = 'static ' + body[0]
        added.append((nm, '\n'.join(body)))
if added:
    sig=[]
    for nm, body in added:
        first=[]
        for l in body.splitlines():
            first.append(l)
            if '{' in l: break
        s=' '.join(x.strip() for x in first); sig.append(s[:s.rindex('{')].strip()+';')
    decls = ('\n/* ---- helpers radare2 also keeps ----\n'
             ' * Duplicated rather than exported: growing radare2\'s public API to serve\n'
             ' * one plugin is what this move exists to undo. */\n' + '\n'.join(sig) + '\n')
    anchor = '/* forward declarations, so the moved bodies keep their original order */\n'
    text = text.replace(anchor, anchor + decls, 1)
    cap.write_text(text + '\n\n' + '\n\n'.join(b for _,b in added) + '\n')
print(f"duplicated {len(added)} shared helpers: {[n for n,_ in added][:8]}")
