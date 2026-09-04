import re, pathlib, sys
F = pathlib.Path('/private/tmp/claude-501/r2-forkcut')

def stripped_lines(text):
    """Blank out string/char literals and comments so brace counting is sound."""
    out=[]; in_block=False
    for l in text.splitlines():
        res=[]; i=0; n=len(l)
        while i<n:
            if in_block:
                k=l.find('*/', i)
                if k<0: i=n; break
                in_block=False; i=k+2; continue
            c=l[i]
            if c=='/' and i+1<n and l[i+1]=='*': in_block=True; i+=2; continue
            if c=='/' and i+1<n and l[i+1]=='/': break
            if c=='"' or c=="'":
                q=c; i+=1
                while i<n and l[i]!=q: i+= 2 if l[i]=='\\' else 1
                i+=1; continue
            res.append(c); i+=1
        out.append(''.join(res))
    return out

DEF = re.compile(r'^(R_API|R_IPI|static)\s+.*?\b([a-z_0-9]+)\s*\(')

def function_spans(path):
    text = path.read_text(errors='replace')
    raw = text.splitlines(); s2 = stripped_lines(text)
    n=len(s2); i=0; spans={}
    while i<n:
        m=DEF.match(s2[i])
        if m and not s2[i].rstrip().endswith(';'):
            # a prototype may span lines: if ';' arrives before '{', it is not a definition
            k=i; proto=False
            while k<n:
                br=s2[k].find('{'); sc=s2[k].find(';')
                if br>=0 and (sc<0 or br<sc): break
                if sc>=0: proto=True; break
                k+=1
            if proto: i=k+1; continue
            d=0; seen=False; j=i
            while j<n:
                d+=s2[j].count('{')-s2[j].count('}')
                if '{' in s2[j]: seen=True
                if seen and d<=0: break
                j+=1
            if j<n:
                spans.setdefault(m.group(2), (i,j)); i=j+1; continue
        i+=1
    return raw, spans

if __name__ == '__main__':
    keep = set(pathlib.Path('/private/tmp/claude-501/keep.txt').read_text().split())
    names = {l.split('\t')[0]: l.split('\t')[1]
             for l in pathlib.Path('/private/tmp/claude-501/movable.txt').read_text().splitlines()
             if l.strip() and l.split('\t')[0] not in keep}
    byfile={}
    for nm, f in names.items(): byfile.setdefault(f, []).append(nm)
    decls=[]; bodies=[]; removed=0
    for f in sorted(byfile):
        p=F/f
        raw, spans = function_spans(p)
        take=[]
        for nm in byfile[f]:
            if nm not in spans:
                print(f"  !! {nm} not found in {f}", file=sys.stderr); continue
            take.append((spans[nm][0], spans[nm][1], nm))
        take.sort()
        bodies.append(f"\n/* ---- moved from {f} ---- */")
        dead=set()
        for a,b,nm in take:
            text=list(raw[a:b+1])
            text[0]=re.sub(r'^(R_API|R_IPI)\s+','static ',text[0])
            if not text[0].lstrip().startswith('static'): text[0]='static '+text[0]
            sig=[]
            for l in text:
                sig.append(l)
                if '{' in l: break
            s=' '.join(x.strip() for x in sig); s=s[:s.rindex('{')].strip()
            decls.append(s+';')
            bodies.append('\n'.join(text))
            dead |= set(range(a,b+1)); removed += b-a+1
        out=[l for i,l in enumerate(raw) if i not in dead]
        tgt=pathlib.Path('/private/tmp/claude-501/stripped')/f
        tgt.parent.mkdir(parents=True, exist_ok=True)
        tgt.write_text('\n'.join(out)+'\n')
    hdr='''/* r2sleigh function-snapshot capture.
 *
 * Moved out of the radare2 fork. Deciding which facts to collect from
 * radare2's analysis, at what granularity and with what proof marking, is
 * r2sleigh's policy, and radare2 does not need it to live inside radare2:
 * everything here runs against radare2's public API while the caller holds
 * anal->lock, which is the one thing the fork still has to provide. */

#include <r_anal.h>
#include <r_core.h>
#include <r_util.h>
#include "snapshot_capture.h"

/* forward declarations, so the moved bodies keep their original order */
'''
    pathlib.Path('/private/tmp/claude-501/snapshot_capture.c').write_text(
        hdr + '\n'.join(decls) + '\n\n' + '\n'.join(bodies) + '\n')
    print(f"moved {len(names)} functions, {removed} lines")
