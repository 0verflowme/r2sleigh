import re, pathlib, sys
sys.path.insert(0,'/private/tmp/claude-501')
from move import function_spans, F

def cut(rel, names, insert=None):
    p=F/rel; raw,spans=function_spans(p); dead=set(); at=None; hit=[]
    for nm in names:
        if nm in spans:
            a,b=spans[nm]; dead|=set(range(a,b+1)); hit.append(nm)
            if insert and at is None: at=a
    out=[]
    for i,l in enumerate(raw):
        if i in dead:
            if insert and i==at: out.append(insert)
            continue
        out.append(l)
    p.write_text('\n'.join(out)+'\n'); return hit

HASH = open('/private/tmp/claude-501/hash_impl.c').read()
ENTRY = open('/private/tmp/claude-501/entry_impl.c').read()

# 1. function.c — drop the snapshot-based hash, add a direct one
print('function.c:', cut('libr/anal/function.c',
    ['r_anal_function_context_hash','r_anal_function_snapshot_free','r_anal_function_snapshot_view']))
p=F/'libr/anal/function.c'
p.write_text(p.read_text().rstrip()+'\n'+HASH)

# 2. canal.c — the core entry point answers with a hash, not a snapshot
print('canal.c:', cut('libr/core/canal.c', ['r_core_function_snapshot_at'], insert=ENTRY))
print('canal.c cb:', cut('libr/core/canal.c', ['plugin_data_refs_revision_cb']))
t=(F/'libr/core/canal.c').read_text()
t=re.sub(r'\tPluginDataRefsRevision revision = \{0\};\n\tif \(!r_core_function_snapshot_at \(\n\t\t\tcore, scope_id, plugin_data_refs_revision_cb, &revision, NULL\)\n\t\t\t\|\| !revision\.captured\n',
         '\tut64 revision = 0;\n\tif (!r_core_function_context_hash (core, scope_id, &revision, NULL)\n', t)
t=re.sub(r'typedef struct \{\n\tut64 revision;\n\tbool captured;\n\} PluginDataRefsRevision;\n\n?','',t)
t=re.sub(r'\brevision\.revision\b','revision',t)
(F/'libr/core/canal.c').write_text(t)

# 3. newprj loader
print('newprj:', cut('libr/core/p/newprj/load.inc.c', ['rprj_artifact_revision_cb']))
p=F/'libr/core/p/newprj/load.inc.c'; t=p.read_text()
t=re.sub(r'\t\tRPrjArtifactRevision revision = \{0\};\n\t\tif \(!r_core_function_snapshot_at \(cur->core, scope_id, rprj_artifact_revision_cb, &revision, NULL\)\n\t\t\t\t\|\| !revision\.captured \|\| !revision\.revision\) \{',
         '\t\tut64 revision = 0;\n\t\tif (!r_core_function_context_hash (cur->core, scope_id, &revision, NULL)) {', t)
t=re.sub(r'\brevision\.revision\b','revision',t); p.write_text(t)

# 4. artifacts
print('artifacts:', cut('libr/core/canal_artifacts.c', ['capture_artifact_snapshot_revision']))
p=F/'libr/core/canal_artifacts.c'; t=p.read_text()
t=re.sub(r'\tArtifactSnapshotRevision revision = \{0\};\n(\treturn replacement->expected_snapshot_revision\n)\t\t&& r_core_function_snapshot_at \(core, replacement->scope_id,\n\t\t\tcapture_artifact_snapshot_revision, &revision, NULL\)\n\t\t&& revision\.captured && revision\.revision ==',
         r'\tut64 revision = 0;\n\1\t\t&& r_core_function_context_hash (core, replacement->scope_id, &revision, NULL)\n\t\t&& revision ==', t)
t=re.sub(r'typedef struct \{[^}]*?\} ArtifactSnapshotRevision;\n\n?','',t,flags=re.S); p.write_text(t)

# 5. cmd_print — the provider gets the function
print('cmd_print:', cut('libr/core/cmd_print.inc.c', ['decompile_snapshot_cb']))
p=F/'libr/core/cmd_print.inc.c'; t=p.read_text()
t=re.sub(r'typedef struct \{[^}]*?\} DecompileSnapshotContext;\n\n?','',t,flags=re.S)
t=re.sub(r'\tDecompileSnapshotContext ctx = \{\n\t\t\.provider = provider,\n\t\};\n\tconst char \*reason = NULL;\n\tif \(!r_core_function_snapshot_at \(\n\t\t\tcore, fcn->addr, decompile_snapshot_cb, &ctx, &reason\)\) \{\n.*?\n\t\}\n\tRCodeMeta \*meta = ctx\.meta;',
         '\tRCodeMeta *meta = provider->decompile (core->anal, fcn);', t, flags=re.S)
p.write_text(t)

# 6. the decompiler plugin ABI takes a function
p=F/'libr/anal/anplugs.c'; t=p.read_text()
t=re.sub(r'R_API RCodeMeta \*r_anal_decompile\(RAnal \*anal, const RAnalFunctionSnapshot \*snapshot\) \{\n\tR_RETURN_VAL_IF_FAIL \(anal && snapshot, NULL\);\n\tRAnalPlugin \*provider = r_anal_decompiler_provider \(anal\);\n\treturn provider\? provider->decompile \(snapshot\): NULL;\n\}',
'''/* Decompile one function with the best-scoring provider.
 *
 * The provider is handed the function rather than a prebuilt snapshot of it.
 * What a decompiler needs to know about a function is the decompiler's
 * business, and shaping radare2's plugin ABI around one plugin's capture
 * format made every other caller carry that format too. */
R_API RCodeMeta *r_anal_decompile(RAnal *anal, RAnalFunction *fcn) {
\tR_RETURN_VAL_IF_FAIL (anal && fcn, NULL);
\tRAnalPlugin *provider = r_anal_decompiler_provider (anal);
\treturn provider? provider->decompile (anal, fcn): NULL;
}''', t)
p.write_text(t)

p=F/'libr/include/r_anal.h'; t=p.read_text()
t=t.replace('typedef RCodeMeta *(*RAnalDecompilerCallback)(const RAnalFunctionSnapshot *snapshot);',
            'typedef RCodeMeta *(*RAnalDecompilerCallback)(RAnal *anal, RAnalFunction *fcn);')
t=re.sub(r'R_API [A-Z_ ]*RCodeMeta \*r_anal_decompile\([^;]*\);',
         'R_API R_OWNED RCodeMeta *r_anal_decompile(RAnal *anal, RAnalFunction *fcn);', t)
p.write_text(t)

p=F/'libr/include/r_core.h'; t=p.read_text()
t=t.replace('typedef RAnalFunctionSnapshotCallback RCoreFunctionSnapshotCallback;\n','')
t=re.sub(r'R_API bool r_core_function_snapshot_at\([^;]*\);',
         'R_API bool r_core_function_context_hash(RCore *core, ut64 function_addr, ut64 *out_hash, const char **reason);', t)
p.write_text(t)
print('surgeries applied')
