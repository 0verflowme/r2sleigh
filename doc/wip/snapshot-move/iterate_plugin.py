import re, subprocess, pathlib, sys
S = pathlib.Path('/private/tmp/claude-501')
INC = str(S/'r2-forkcut-install/include/libr')
CC = ['gcc','-fsyntax-only','-std=gnu99','-I'+INC,'-I'+INC+'/sdb',
      '-I'+str(S/'r2-forkcut/subprojects/sdb/include'),'-I'+str(S),str(S/'snapshot_capture.c')]
for rnd in range(1, 16):
    subprocess.run([str(S/'pipeline.sh')], capture_output=True, cwd=S)
    out = subprocess.run(CC, capture_output=True, text=True).stderr
    n = out.count('error:')
    if n == 0:
        print(f"ROUND {rnd}: plugin capture compiles"); break
    types = sorted(set(re.findall(r"unknown type name '([A-Za-z_0-9]+)'", out)))
    dups  = sorted(set(re.findall(r"call to undeclared function '([a-z_0-9]+)'", out)))
    clash = sorted(set(re.findall(r"static declaration of '([a-z_0-9]+)'", out)))
    incomplete = sorted(set(re.findall(r"incomplete definition of type '(?:const )?([A-Za-z_0-9]+)'", out)))
    undeclared_types = sorted({n for n in re.findall(r"use of undeclared identifier '([A-Za-z_0-9]+)'", out) if n[:1].isupper()})
    types = sorted(set(types) | set(undeclared_types))
    print(f"ROUND {rnd}: {n} errors | types={len(types)} dups={len(dups)} clash={len(clash)} incomplete={len(incomplete)}")
    progressed = False
    if types or incomplete:
        r = subprocess.run([sys.executable, str(S/'carry_types.py')] + types + incomplete,
                           capture_output=True, text=True)
        print('   ' + r.stdout.strip()); progressed = True
    if clash:
        p = S/'clash.txt'
        prev = set(p.read_text().split()) if p.exists() else set()
        if not set(clash) <= prev:
            p.write_text('\n'.join(sorted(prev | set(clash))) + '\n')
            print(f"   clash list now {len(prev | set(clash))}"); progressed = True
    lower_undeclared = sorted({n for n in re.findall(r"use of undeclared identifier '([a-z_0-9]+)'", out)})
    force = sorted(set(dups) | set(lower_undeclared))
    if force:
        fp = S/'dupforce.txt'
        prev = set(fp.read_text().split()) if fp.exists() else set()
        if not set(force) <= prev:
            fp.write_text('\n'.join(sorted(prev | set(force))) + '\n')
            print(f"   dup list now {len(prev | set(force))}"); progressed = True
        else:
            print(f"   still undeclared: {force[:6]}")
    if not progressed:
        print("   no progress; stopping"); break
