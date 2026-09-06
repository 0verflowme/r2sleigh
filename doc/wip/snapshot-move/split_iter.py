import re, subprocess, pathlib, sys
sys.path.insert(0,'/private/tmp/claude-501')
F = pathlib.Path('/private/tmp/claude-501/r2-forkcut')
REL = sys.argv[1] if len(sys.argv)>1 else 'test/unit/test_anal_function.c'
BIN = pathlib.Path(REL).stem
DEFANY = re.compile(r'^[A-Za-z_].*\b([a-z_0-9]+)\s*\(')

def enclosing(raw, line0):
    """Name of the function whose definition starts at or above line0."""
    for i in range(line0, -1, -1):
        m = DEFANY.match(raw[i])
        if m and not raw[i].rstrip().endswith(';') and '(' in raw[i]:
            return m.group(1)
    return None

for round in range(1, 12):
    r = subprocess.run(['make','-C','test/unit','bin/'+BIN],
                       cwd=F, capture_output=True, text=True)
    errs = re.findall(re.escape(pathlib.Path(REL).name)+r':(\d+):\d+: error:', r.stdout + r.stderr)
    und  = re.findall(r'"_([a-z_0-9]+)", referenced from', r.stdout + r.stderr)
    if not errs and not und:
        print(f"round {round}: {BIN} builds"); break
    raw = (F/REL).read_text().splitlines()
    extra = set()
    for e in errs:
        nm = enclosing(raw, int(e)-1)
        if nm: extra.add(nm)
    for u in und:
        for i,l in enumerate(raw):
            if re.search(r'\b'+re.escape(u)+r'\b', l):
                nm = enclosing(raw, i)
                if nm: extra.add(nm)
                break
    if not extra:
        print(f"round {round}: stuck; errs={errs[:3]} und={und[:3]}"); break
    from split_tests import split
    mv, st = split(REL, extra_move=extra)
    old = pathlib.Path('/private/tmp/claude-501/staged_plugin_tests.c')
    old.write_text(old.read_text() + '\n\n' + '\n\n'.join(st) + '\n')
    print(f"round {round}: moved {len(mv)} more ({len(extra)} seeds)")
