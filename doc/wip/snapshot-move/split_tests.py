import re, pathlib, sys
sys.path.insert(0,'/private/tmp/claude-501')
from move import stripped_lines
F = pathlib.Path('/private/tmp/claude-501/r2-forkcut')
SNAP = re.compile(r'RAnalFunctionSnapshot|RAnalSnapshot|RAnalFcnSlot|RAnalFcnContext'
                  r'|r_anal_function_snapshot|R_ANAL_FUNCTION_SNAPSHOT|R_ANAL_SNAPSHOT'
                  r'|RAnalFunctionImageSnapshot|snapshot_test_')
DEF = re.compile(r'^(?:static\s+|R_API\s+|R_IPI\s+)?[A-Za-z_][A-Za-z_0-9]*[ *]+.*?\b([a-z_0-9]+)\s*\(')

def spans_of(path):
    raw = path.read_text().splitlines(); s2 = stripped_lines('\n'.join(raw))
    n=len(s2); i=0; out={}
    while i<n:
        m=DEF.match(s2[i])
        if m and not s2[i].rstrip().endswith(';'):
            k=i; proto=False
            while k<n:
                br=s2[k].find('{'); sc=s2[k].find(';')
                if br>=0 and (sc<0 or br<sc): break
                if sc>=0: proto=True; break
                k+=1
            if proto: i=k+1; continue
            d=0;seen=False;j=i
            while j<n:
                d+=s2[j].count('{')-s2[j].count('}')
                if '{' in s2[j]: seen=True
                if seen and d<=0: break
                j+=1
            out.setdefault(m.group(1),(i,j)); i=j+1; continue
        i+=1
    return raw, out

def split(relpath, extra_move=()):
    p = F/relpath
    raw, spans = spans_of(p)
    move = {nm for nm,(a,b) in spans.items() if SNAP.search('\n'.join(raw[a:b+1]))}
    move |= {n for n in extra_move if n in spans}
    move -= {'main','all_tests'}
    # a stayer that calls a mover must move too
    changed=True
    while changed:
        changed=False
        for nm,(a,b) in spans.items():
            if nm in move: continue
            body='\n'.join(raw[a:b+1])
            if any(re.search(r'\b'+re.escape(m)+r'\s*\(', body) for m in move):
                move.add(nm); changed=True
    dead=set(); staged=[]
    for nm in sorted(move, key=lambda n: spans[n][0]):
        a,b=spans[nm]; dead|=set(range(a,b+1)); staged.append('\n'.join(raw[a:b+1]))
    text='\n'.join(l for i,l in enumerate(raw) if i not in dead)+'\n'
    for nm in move:
        text=re.sub(r'^\s*[a-z_]+ \('+re.escape(nm)+r'\);\n','',text,flags=re.M)
    p.write_text(text)
    return move, staged

if __name__ == '__main__':
    allstaged=[]
    for rel in ['test/unit/test_anal_function.c']:
        mv, st = split(rel)
        print(f"{rel}: moved {len(mv)} functions")
        allstaged += st
    old = pathlib.Path('/private/tmp/claude-501/staged_plugin_tests.c')
    old.write_text(old.read_text() + '\n\n/* ---- from test_anal_function.c ---- */\n\n' + '\n\n'.join(allstaged) + '\n')
    print(f"staged total now {old.read_text().count(chr(10))} lines")
