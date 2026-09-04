#!/bin/zsh
set -e
cd /private/tmp/claude-501/r2-forkcut
git checkout -- libr/
rm -rf /private/tmp/claude-501/stripped
python3 /private/tmp/claude-501/move.py
cp -r /private/tmp/claude-501/stripped/libr/. libr/
python3 /private/tmp/claude-501/surgeries.py
python3 /private/tmp/claude-501/finish_move.py
# dup_shared must copy the shared helpers before prune_dead deletes them,
# and strip_types must run after prune_dead removes the last references.
python3 /private/tmp/claude-501/dup_shared.py
python3 /private/tmp/claude-501/prune_dead.py
python3 /private/tmp/claude-501/strip_types.py
python3 - <<'PY'
import pathlib
p = pathlib.Path('/private/tmp/claude-501/snapshot_capture.c'); t = p.read_text()
if 'r2sleigh_function_snapshot_take' not in t:
    t += pathlib.Path('/private/tmp/claude-501/capture_entry.c').read_text()
    p.write_text(t)
print(f"snapshot_capture.c: {t.count(chr(10))} lines")
PY
