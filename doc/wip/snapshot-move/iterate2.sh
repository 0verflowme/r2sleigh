#!/bin/zsh
W=/private/tmp/claude-501/r2-forkcut
FILES=(libr/anal/function.c libr/anal/type.c libr/anal/cc.c libr/anal/fcn.c libr/anal/anplugs.c
       libr/anal/var.c libr/anal/xrefs.c libr/anal/meta.c libr/core/canal.c
       libr/core/canal_artifacts.c libr/util/utype.c libr/flag/flag.c)
for round in {1..12}; do
  /private/tmp/claude-501/pipeline.sh >/dev/null 2>&1 || { echo "pipeline failed"; exit 1; }
  cd $W
  bad=()
  for f in $FILES; do
    [[ -f $f ]] || continue
    e=$(gcc -fsyntax-only -std=gnu99 -Ilibr/include -Ishlr -Ishlr/sdb/src -Ilibr -I. "$f" 2>&1 \
      | grep -oE "(call to undeclared function|use of undeclared identifier) '[a-z_0-9]+'" \
      | grep -oE "'[a-z_0-9]+'" | tr -d "'")
    for x in ${(f)e}; do bad+=$x; done
  done
  bad=(${(u)bad})
  if (( ${#bad} == 0 )); then echo "ROUND $round: fork converged"; break; fi
  before=$(grep -c . /private/tmp/claude-501/movable.txt)
  python3 - "$bad[@]" <<'PY'
import sys, pathlib
bad=set(sys.argv[1:])
p=pathlib.Path('/private/tmp/claude-501/movable.txt')
rows=[l for l in p.read_text().splitlines() if l.strip() and l.split('\t')[0] not in bad]
p.write_text('\n'.join(rows)+'\n')
k=pathlib.Path('/private/tmp/claude-501/keep.txt')
k.write_text(k.read_text().rstrip()+'\n'+'\n'.join(bad)+'\n')
PY
  after=$(grep -c . /private/tmp/claude-501/movable.txt)
  echo "ROUND $round: ${#bad} undefined, movable $before -> $after"
  [[ $before == $after ]] && { echo "  STUCK: $bad"; break; }
done
