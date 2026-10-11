import hashlib
import json
from pathlib import Path
import subprocess
import sys

root = Path('E:/ABRL/worktrees/research-online-book')
py = 'C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
base = root / 'tmp/online-support-reader-tool-preparation-20261012'
gatebase = root / 'tmp/online-support-owner-repaired-gates-20261012'
head = '95cfc51fa11619217f8153614d5b5b8a6c04aa2d'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_bytes())
prepared = base / 'input-spec-prepared-v7.json'
assert digest(prepared) == 'c4d1f3df4a6757d842b8b559fe9d48967a6c2f68faef7e50eb82accf2933934c'
spec = load(prepared)
assert spec['ready_for_execution'] is False and spec['head'] == head
spec['ready_for_execution'] = True
site = root / 'tmp/online-support-site-20261012-verified-v2'
spec['evidence_required']['isolated_site'] = str(site.resolve())
for label in ['contributor-actual-pr-base-v1','process-memory-v1','production-root-v1','shared-Tests-v1','full-harness-v1','combined-axiom-audit-v1','plain-site-build-v1','plain-site-check-v1','verified-site-build-v1','verified-site-check-v1']:
    path = gatebase / label / 'receipt.json'
    row = load(path)
    assert row['actual_exit'] == 0 and row['command_started'] and row['capture_integrity_ok'] and row['complete_source_path_set_and_RAW_unchanged']
    assert row['pre_git']['HEAD'] == row['post_git']['HEAD'] == head
    assert row['pre_git']['status_porcelain_v1_z_hex'] == row['post_git']['status_porcelain_v1_z_hex'] == ''
for role,label in [('full_harness','full-harness-v1'),('site_build_verified','verified-site-build-v1'),('site_check','verified-site-check-v1')]:
    path = gatebase / label / 'receipt.json'
    spec['evidence_required'][role] = {'path':str(path.resolve()),'sha256':digest(path)}
fallback = root / 'tmp/online-support-resume-20261012/browser-capability-observation-v1.json'
assert load(fallback)['available_runtime_cannot_navigate_local_site'] is True
spec['evidence_required']['browser_unavailable_observation'] = {'path':str(fallback.resolve()),'sha256':digest(fallback),'provenance':'Actual earlier runtime capability discovery; no new browser discovery claimed.'}
recorder = root / 'runs/online-ch2-b4-strong-convex-support-20261011/prepared/capture-gate-v3.py'
spec['recorder_sha256'] = digest(recorder)
assert spec['recorder_sha256'] == '40faf086d3662f68b3e91da0cea913216afe2e5e60d89217c0ae6d830a2eb273'
spec['root_execution_scope'] = 'Exact reviewed v7 spec/v4 structural/v6 browser plus completed clean95c gates, no source or semantic changes.'
def create(path,value):
    with path.open('x',encoding='utf-8',newline='\n') as out:
        json.dump(value,out,ensure_ascii=False,indent=2)
        out.write('\n')
execution = base / 'input-spec-execution-structural-v2.json'
create(execution,spec)
gate = Path(spec['evidence_required']['full_harness']['path'])
result = base / 'structural-result-v2.json'
command = [py,'-B','-X','utf8',str(base/'check-support-structure-v4.py'),'--root',str(root),'--baseline',str(root/spec['baseline_registry']),'--site',str(site),'--gate',str(gate),'--gate-sha256',digest(gate),'--head',head,'--spec',str(execution),'--spec-sha256',digest(execution),'--output',str(result)]
print(json.dumps({'argv':command}),flush=True)
proc = subprocess.run(command,cwd=root)
if proc.returncode:
    sys.exit(proc.returncode)
row = load(result)
assert row['actual_exit'] == 0 and row['pre_git'] == row['post_git']
spec['evidence_required']['structural_result'] = {'path':str(result.resolve()),'sha256':digest(result)}
browser_spec = base / 'input-spec-execution-browser-v2.json'
create(browser_spec,spec)
browser = base / 'capture-support-reader-v6.cjs'
assert digest(browser) == spec['browser_helper_sha256']
node = 'C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe'
argv = [node,str(browser),'http://127.0.0.1:8896/chapters/online-ogd/',str(base/'actual-render-v2'),str(base/'isolated-profile-v2'),str(site/'books/registry.json'),str(root),str(site),str(gate),digest(gate),head,str(browser_spec),digest(browser_spec)]
create(Path(__file__).parent/'browser-execution-argv-v2.json',{'argv':argv,'execution_performed':False,'server_required':'127.0.0.1:8896 serving exact verified-v2 site','source_head':head})
print(json.dumps({'structural_result':str(result),'browser_argv_prepared':True}))
