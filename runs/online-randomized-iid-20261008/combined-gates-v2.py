from common_integrated_v2 import *

fixed_integrated()
baseline=Path('tmp/online-iid-benchmark-site-v9/books/registry.json')
registry=load(baseline)
assert len(registry['nodes'])==10923
write(RUN/'registry-base-snapshot-v2.json',baseline.read_bytes())
write(RUN/'registry-base-provenance-v2.json',dict(source=baseline.as_posix(),sha256=sha(baseline),
    prior_shared_nodes=len(registry['nodes']),new_package_Lean_gate=False,
    statement='Prior package local registry is used only as an exact old-node preservation baseline.'))
trials=[json.loads(line) for line in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines() if line.strip()]
trials=[r for r in trials if r.get('task')==TASK]
assert trials
write(RUN/'candidate-scoped-trials-v2.jsonl','\n'.join(json.dumps(r,ensure_ascii=False) for r in trials))
terminal=load(CONTRACT/'targets-v2.json')['rows'][6]
for command in ['frontier-refresh','frontier-shadow','check']:
    native(command+'-help-v2',command,'--help')
native('candidate-frontier-refresh-v2','frontier-refresh','--root-objective',
    'Persistent Orabona Chapters1-16; private-seed/subordinate-information finite IID producer only',
    '--leaf',TASK,'--kind','lean','--statement',terminal['header'],'--declaration',terminal['name'],'--file',PUBLIC,
    '--source-status','source-reviewed','--leaf-status','gate-pending','--dependency','review:source-body:accepted',
    '--dependency','lean:'+PRE+'private_seed_past_independent:compiled',
    '--dependency','lean:'+PRE+'predictable_private_seed_expectedFixed_excess:compiled',
    '--trials',RUN/'candidate-scoped-trials-v2.jsonl','--output',RUN/'candidate-frontier-v2.json','--shadow-status','pending')
native('candidate-frontier-shadow-v2','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v2.jsonl',
    '--memory-digest',RUN/'memory_digest-candidate-v2.md','--frontier',RUN/'candidate-frontier-v2.json')
gate('combined-root-v2','lake','build')
gate('combined-Tests-v2','lake','build','Tests')
native('full-harness-v2','check')
write(RUN/'combined-gates-v2.json',dict(status='Actual combined root/Tests/full harness/own scoped shadow passed.',
    root_log_sha256=sha(RUN/'combined-root-v2.log'),Tests_log_sha256=sha(RUN/'combined-Tests-v2.log'),
    harness_log_sha256=sha(RUN/'full-harness-v2.log'),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    contributor='Committed exact-base production diff gate REQUIRED; zero-path command exit is not acceptance.',
    globalSGB_unchanged=True,site_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
fixed_integrated()
print('Actual combined gates passed; committed contributor/shared registry/clean site/pixels/FINAL/native/PR remain.')
